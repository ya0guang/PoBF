use core::marker::PhantomData;

use crate::types::*;
use prusti_contracts::*;
use sgx_types::error::SgxResult;
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

// Some helper pure functions ofr `SgxResult` type...
// HACK: These seem to be the only way to let Prusti correctly verify the result...
#[cfg(feature = "use_prusti")]
#[pure]
#[allow(unused)]
pub fn is_ok_generic<T>(input: &SgxResult<T>) -> bool {
    if let Ok(_) = input {
        true
    } else {
        false
    }
}

#[cfg(feature = "use_prusti")]
#[pure]
#[allow(unused)]
pub fn is_err_generic<T>(input: &SgxResult<T>) -> bool {
	!is_ok_generic(input)
}

#[cfg(feature = "use_prusti")]
#[pure]
#[allow(unused)]
pub fn is_ok<D: EncDec<K>, K: Default>(input: &SgxResult<D>) -> bool {
    if let Ok(_) = input {
        true
    } else {
        false
    }
}

#[cfg(feature = "use_prusti")]
#[pure]
#[allow(unused)]
pub fn is_err<D: EncDec<K>, K: Default>(input: &SgxResult<D>) -> bool {
    !is_ok(input)
}

#[cfg(feature = "use_prusti")]
#[pure]
#[allow(unused)]
pub fn is_ok_aes(input: &SgxResult<VecAESData>) -> bool {
    if let Ok(_) = input {
        true
    } else {
        false
    }
}

#[cfg(feature = "use_prusti")]
#[pure]
#[allow(unused)]
pub fn is_err_aes(input: &SgxResult<VecAESData>) -> bool {
    !is_ok(input)
}