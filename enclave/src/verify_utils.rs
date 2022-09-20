use core::marker::PhantomData;

use crate::types::*;
#[cfg(feature = "use_prusti")]
use crate::userfunc::vec_play;
use crate::{ocall::*, ocall_log};
use alloc::vec::Vec;
use prusti_contracts::*;
use sgx_types::error::*;
use zeroize::Zeroize;

/// A bogus computation_task for Prusti verification since Prusti does not support higher-order
/// functions. So we currently verify the framework and the computation_task separately.
pub struct ComputationTask<D, K>
where
    D: EncDec<K> + From<VecWrapperU8> + Into<VecWrapperU8>,
    K: Default + Zeroize,
{
    inner: PhantomData<D>,
    key: PhantomData<K>,
}

impl<D, K> ComputationTask<D, K>
where
    D: EncDec<K> + From<VecWrapperU8> + Into<VecWrapperU8>,
    K: Default + Zeroize,
{
    /// Invokes the computation task. Because we cannot use higher-order functions when
    /// we try to perform verification using Prusti / creusot, we define another function here
    /// for the convenience of verification task.
    #[cfg(feature = "use_prusti")]
    #[allow(unused)]
    pub fn do_compute(&self, data_in: D) -> D {
        let data = VecWrapperU8::from_data(data_in);

        // Should pass the assertion.
        assert!(data.tainted());

        // It is user's duty to control the range of u8.
        // We show that the implementation is consistent with the model.
        // _0_quant_0) + 1 <= 255 not hold.
        #[cfg(feature = "enable_task")]
        {
            let res = vec_play(&data, 1);
            D::from(res)
        }

        #[cfg(not(feature = "enable_task"))]
        {
            D::from(data)
        }
    }

    #[trusted]
    #[allow(unused)]
    pub fn new() -> Self {
        Self {
            inner: PhantomData,
            key: PhantomData,
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
    #[allow(unused)]
    pub fn new() -> Self {
        Self {
            inner: Vec::new(),
            secret_tainted: true,
        }
    }

    #[allow(unused)]
    #[ensures((&result).secret_tainted == secret_tainted)]
    pub fn from_raw(inner: Vec<u8>, secret_tainted: bool) -> Self {
        Self {
            inner,
            secret_tainted,
        }
    }

    /// Converts a type that meets the given contraints into `VecWrapperu8`. The reason why we do not
    /// use trait method is because Prusti has error verifying it.
    #[trusted]
    #[ensures((&result).tainted())]
    #[allow(unused)]
    pub fn from_data<D, K>(input: D) -> Self
    where
        D: EncDec<K> + From<VecWrapperU8> + Into<VecWrapperU8>,
    {
        input.into()
    }

    #[requires(!(&self).tainted())]
    #[allow(unused)]
    pub fn log(&self) {
        let mut i = 0usize;

        while i < self.inner.len() {
            ocall_log!("{}: {}.", i, self.inner[i]);
            i += 1;
        }
    }

    #[requires(!(&self).tainted())]
    #[allow(unused)]
    pub fn log_index(&self, index: usize) {
        ocall_log!("{}: {}", index, self.inner[index]);
    }

    #[cfg(feature = "leak_net")]
    #[requires(!(&self).tainted())]
    #[allow(unused)]
    pub fn send_to_network(&self, addr: &str) {
        use std::net::TcpStream;
        match TcpStream::connect(addr) {
            Ok(mut stream) => stream.write(&self.inner).unwrap(),
            Err(_) => (),
        }
    }

    #[cfg(feature = "leak_file")]
    #[requires(!(&self).tainted())]
    #[allow(unused)]
    pub fn write_to_file(&self, path: &str) {
        use std::fs::File;
        let mut f = File::create(path).unwrap();
        f.write_all(&self.inner).unwrap();
    }

    // Cannot reverse a tainted vec.
    #[requires(!(&self).tainted())]
    #[ensures(old(&self).tainted() != (&self).tainted())]
    #[allow(unused)]
    pub fn reverse_tag(&mut self) {
        self.secret_tainted = !self.secret_tainted;
    }

    #[pure]
    #[ensures(result == (&self).secret_tainted)]
    #[allow(unused)]
    pub fn tainted(&self) -> bool {
        self.secret_tainted
    }

    #[trusted]
    #[pure]
    #[allow(unused)]
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
    #[allow(unused)]
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

    #[requires(0 <= index && index < self.len())]
    #[ensures(*result == *self.lookup(index))]
    #[allow(unused)]
    pub fn index(&self, index: usize) -> &u8 {
        &self.inner[index]
    }

    #[trusted]
    #[ensures(*self.lookup(index) == new_value)]
    #[ensures(old(&self).tainted() == (&self).tainted())]
    #[allow(unused)]
    pub fn modify(&mut self, index: usize, new_value: u8) {
        self.inner[index] = new_value;
    }

    #[ensures((&result).1 == old(&self).secret_tainted)]
    pub fn take(self) -> (Vec<u8>, bool) {
        (self.inner, self.secret_tainted)
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
