#[cfg(feature = "use_prusti")]
use core::marker::PhantomData;

use crate::{ocall::*, ocall_log};
use crate::{ocall_print, types::*};
use alloc::vec::Vec;
use prusti_contracts::*;
use sgx_types::error::*;

/// A bogus computation_task for Prusti verification since Prusti does not support higher-order
/// functions. So we currently verify the framework and the computation_task separately.
pub struct ComputationTask<T: Sized> {
    _inner: PhantomData<T>,
}

impl<T: Sized> ComputationTask<T> {
    /// Invokes the computation task (dummy). Because we cannot use higher-order functions when
    /// we try to perform verification using Prusti / creusot, we define a dummy operation here
    /// for the convenience of verification task.
    #[trusted]
    pub fn do_compute(&self, data_in: T) -> T {
        // Simply does nothing and returns the raw data.
        data_in
    }

    #[trusted]
    pub fn new() -> Self {
        Self {
            _inner: PhantomData,
        }
    }
}

/// A wrapper that contains the `Vec<T>` type. Prusti cannot verify raw `Vec` because indexing into it causes some problems.
/// We need to either wrap this as a struct or use `#[extern_spec]` to notify Prusti that `Vec` is imported from external
/// libraries, and that it should not attempt to verify internal methods.
///
/// # Example
/// ```rust
/// 	let v = VecWrapper>U8:new();
/// 	v.push(1);
/// 	println!("First element is :{}", v.index(0));
/// ```
pub struct VecWrapperU8 {
    inner: Vec<u8>,
    secret_tainted: bool,
}

impl VecWrapperU8 {
    #[trusted]
    #[ensures(result.len() == 0)]
    #[ensures((&result).tainted())]
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            secret_tainted: true,
        }
    }

    #[requires(!(&self).tainted())]
    pub fn log(&self) {
        let mut i = 0usize;

        while i < self.inner.len() {
            ocall_log!("{}: {}.", i, self.inner[i]);
            i += 1;
        }
    }

    #[requires(!(&self).tainted())]
    pub fn log_index(&self, index: usize) {
        ocall_log!("{}: {}", index, self.inner[index]);
    }

    // Cannot reverse a tainted vec.
    #[requires(!(&self).tainted())]
    #[ensures(old(&self).tainted() != (&self).tainted())]
    pub fn reverse_tag(&mut self) {
        self.secret_tainted = !self.secret_tainted;
    }

    #[trusted]
    #[pure]
    #[ensures(result == (&self).secret_tainted)]
    #[allow(unused)]
    pub fn tainted(&self) -> bool {
        self.secret_tainted
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(forall (
		|i : usize| (0 <= i && i < old(self.len()) ==> *self.lookup(i) == *(old(&self).lookup(i)))
	))]
    #[ensures(*self.lookup(self.len() - 1) == value)]
    #[ensures(old(&self).tainted() == (&self).tainted())]
    pub fn push(&mut self, value: u8) {
        self.inner.push(value);
    }

    /// This function is important when indexing the `Vec` because Prusti cannot verify LHS slice reference type, i.e., LHS &T.
    ///
    /// # Example:
    /// ```rust
    /// 	let mut v = vec![1, 2, 3];
    /// 	// Prusti panicks here:
    /// 	// 		error: [Prusti: unsupported feature] Non-slice LHS type '&i32' not supported yet
    /// 	let _ = v[0];
    ///
    /// ```
    #[trusted]
    #[pure]
    #[allow(unused)]
    pub fn lookup(&self, index: usize) -> &u8 {
        &self.inner[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(*result == *self.lookup(index))]
    pub fn index(&self, index: usize) -> &u8 {
        &self.inner[index]
    }

    #[trusted]
    #[ensures(*self.lookup(index) == new_value)]
    #[allow(unused)]
    pub fn modify(&mut self, index: usize, new_value: u8) {
        self.inner[index] = new_value;
    }
}

// Some helper pure functions ofr `SgxResult` type...

#[pure]
#[allow(unused)]
pub fn is_ok_generic<T>(input: &SgxResult<T>) -> bool {
    if let Ok(_) = input {
        true
    } else {
        false
    }
}

#[pure]
#[allow(unused)]
pub fn is_ok_default<D: EncDec<K>, K: Default>(input: &SgxResult<D>) -> bool {
    if let Ok(_) = input {
        true
    } else {
        false
    }
}

#[pure]
#[allow(unused)]
pub fn is_ok_aes(input: &SgxResult<VecAESData>) -> bool {
    if let Ok(_) = input {
        true
    } else {
        false
    }
}

#[pure]
#[allow(unused)]
pub fn is_err_aes(input: &SgxResult<VecAESData>) -> bool {
    !is_ok_aes(input)
}
