use core::marker::PhantomData;

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

    pub fn new() -> Self {
        Self {
            _inner: PhantomData,
        }
    }
}

#[cfg(feature = "use_prusti")]
#[extern_spec]
impl<T> SgxResult<T> {
    /// A pure logical function for verification. Rust will desugar the precondition statement
    ///   ```rust
    ///   #[ensures(result.is_ok())]
    ///   ```
    /// to a non-pure function, which will make Prusti reject the code.
    #[pure]
    #[ensures(matches!(*self, Ok(_)) == result)]
    #[allow(unused_must_use)]
    #[allow(unused)]
    pub fn is_ok(&self) -> bool;

    /// A pure logical function that calls `unwrap` method on `Result` type.
    #[pure]
    #[requires(self.is_ok())]
    #[allow(unused)]
    pub fn unwrap(self) -> T;
}
