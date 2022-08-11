use core::arch::asm;
use crate::fnoption::FnOption;
use crate::hide::{hide_mem, hide_ptr};

/// Once arguments are classified, the registers get assigned for passing as follows:
///
/// 1. If the class is MEMORY, pass the argument on the stack.
/// 2. If the class is INTEGER, the next available register of the sequence
///    %rdi, %rsi, %rdx, %rcx, %r8 and %r9 is used.
#[inline]
fn clean_registers() {
  unsafe {
    asm!("xor rbx, rbx /* {0} */", out(reg) _);
    asm!("xor rcx, rcx /* {0} */", out(reg) _);
    asm!("xor rdx, rdx /* {0} */", out(reg) _);
    asm!("xor rdi, rdi /* {0} */", out(reg) _);
    asm!("xor rsi, rsi /* {0} */", out(reg) _);
    asm!("xor r8, r8 /* {0} */", out(reg) _);
    asm!("xor r9, r9 /* {0} */", out(reg) _);
    asm!("xor r10, r10 /* {0} */", out(reg) _);
    asm!("xor r11, r11 /* {0} */", out(reg) _);
    asm!("xor r12, r12 /* {0} */", out(reg) _);
    asm!("xor r13, r13 /* {0} */", out(reg) _);
    asm!("xor r14, r14 /* {0} */", out(reg) _);
    asm!("xor r15, r15 /* {0} */", out(reg) _);
  }
}

/// Calls a closure and overwrites its stack on return.
///
/// This function calls `clear_stack` after calling the passed closure,
/// taking care to prevent either of them being inlined, so the stack
/// used by the closure will be overwritten with zeros (as long as a
/// large enough number of `pages` is used).
///
/// For technical reasons, this function can be used only with `Fn` or
/// `FnMut`. If all you have is a `FnOnce`, use the auxiliary function
/// `clear_stack_on_return_fnonce` instead.
///
/// # Example
///
/// ```
/// # use clear_on_drop::clear_stack_on_return;
/// # fn encrypt(input: &[u8]) -> Vec<u8> { input.to_owned() }
/// let input = b"abc";
/// let result = clear_stack_on_return(1, || encrypt(input));
/// ```
#[inline]
pub fn clear_stack_on_return<F, R>(pages: usize, mut f: F, clean_regs: bool) -> R
  where
      F: FnMut() -> R,
{
  let _clear = ClearStackOnDrop { pages, clean_regs };
  // Do not inline f to make sure clear_stack uses the same stack space.
  let hidden_func = hide_ptr::<&mut dyn FnMut() -> R>(&mut f);

  // TODO: Calculate the estimated size of the stack frame.

  hidden_func()
}

/// Calls a closure and overwrites its stack on return.
///
/// This function is a variant of `clear_stack_on_return` which also
/// accepts `FnOnce`, at the cost of being slightly slower.
///
/// # Example
///
/// ```
/// # use clear_on_drop::clear_stack_on_return_fnonce;
/// # fn encrypt(input: Vec<u8>) -> Vec<u8> { input }
/// let input = vec![97, 98, 99];
/// let result = clear_stack_on_return_fnonce(1, || encrypt(input));
/// ```
#[inline]
pub fn clear_stack_on_return_fnonce<F, R>(pages: usize, f: F, clean_regs: bool) -> R
  where
      F: FnOnce() -> R,
{
  let mut f = FnOption::new(f);
  clear_stack_on_return(pages, || f.call_mut(), clean_regs).unwrap()
}

struct ClearStackOnDrop {
  pages: usize,
  clean_regs: bool,
}

impl Drop for ClearStackOnDrop {
  #[inline]
  fn drop(&mut self) {
    // Do not inline clear_stack.
    hide_ptr::<fn(usize, bool)>(clear_stack)(self.pages, self.clean_regs);
  }
}

/// Overwrites a few pages of stack.
///
/// This function will overwrite `pages` 4096-byte blocks of the stack
/// with zeros.
///
/// ```asm
/// call    __rust_probestack
/// sub     rsp, rax
/// test    rdi, rdi
/// jz      short loc_188C8
/// ```
pub fn clear_stack(pages: usize, clean_regs: bool) {
  // When the cleaner is about to finish, we write garbage data to all the registers.
  if pages == 0 && clean_regs {
    clean_registers();
  } else {
    let mut buf = [0u8; 4096];
    hide_mem(&mut buf); // prevent moving after recursive call
    clear_stack(pages - 1, clean_regs);
    hide_mem(&mut buf); // prevent reuse of stack space for call
  }
}
