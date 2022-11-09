#![cfg_attr(feature = "sgx", no_std)]

extern crate alloc;

use alloc::string::String;
use alloc::vec::Vec;
use core::time::Duration;
use polybench_rs::datamining::*;
use polybench_rs::linear_algebra::blas::*;
use polybench_rs::linear_algebra::kernels::*;
use polybench_rs::linear_algebra::solvers::*;
use polybench_rs::medley::*;
use polybench_rs::stencils::*;

pub struct BenchResult {
    pub inner: Vec<(String, Vec<(String, Duration)>)>,
}

impl BenchResult {
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }
}

impl core::fmt::Debug for BenchResult {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "\n")?;

        for bench_type in self.inner.iter() {
            write!(f, "========== {} ==========\n", bench_type.0)?;

            for entry in bench_type.1.iter() {
                write!(f, "{}: {} us\n", entry.0, entry.1.as_micros())?;
            }

            write!(f, "\n")?;
        }

        Ok(())
    }
}

/// Invokes `polybench_run` but the parameter is not used.
pub fn private_computation(input: Vec<u8>) -> Vec<u8> {
  let _ = polybench_run(&|| 0);

  input
} 

/// Dimension too large => Memory consumption large => Enclave crash...
/// Performs the polybench and returns the grouped result.
/// The detailed benchmarks can be generated using a timing function `f`.
pub fn polybench_run(f: &dyn Fn() -> u64) -> BenchResult {
    let mut res = BenchResult::new();

    // linear algebra.
    res.inner.push((String::from("Linear Algebra"), Vec::new()));
    res.inner[0].1.push((
        String::from("kernels::2mm"),
        _2mm::bench::<1000, 1000, 1000, 1000>(f),
    ));
    res.inner[0].1.push((
        String::from("kernels::3mm"),
        _3mm::bench::<200, 225, 250, 275, 300>(f),
    ));
    res.inner[0]
        .1
        .push((String::from("kernels::atax"), atax::bench::<100, 200>(f)));
    res.inner[0]
        .1
        .push((String::from("kernels::bicg"), bicg::bench::<100, 200>(f)));
    res.inner[0].1.push((
        String::from("kernels::doitgen"),
        doitgen::bench::<100, 100, 20>(f),
    ));

    // blas.
    res.inner[0]
        .1
        .push((String::from("blas::gemm"), gemm::bench::<100, 100, 100>(f)));
    res.inner[0]
        .1
        .push((String::from("blas::gemver"), gemver::bench::<100>(f)));
    res.inner[0]
        .1
        .push((String::from("blas::gesummv"), gesummv::bench::<100>(f)));
    res.inner[0]
        .1
        .push((String::from("blas::symm"), symm::bench::<100, 100>(f)));
    res.inner[0]
        .1
        .push((String::from("blas::syr2k"), syr2k::bench::<100, 100>(f)));
    res.inner[0]
        .1
        .push((String::from("blas::syrk"), syrk::bench::<100, 100>(f)));
    res.inner[0]
        .1
        .push((String::from("blas::trmm"), trmm::bench::<100, 100>(f)));

    // solvers.
    res.inner[0]
        .1
        .push((String::from("solvers::cholesky"), cholesky::bench::<100>(f)));
    res.inner[0]
        .1
        .push((String::from("solvers::durbin"), durbin::bench::<100>(f)));
    res.inner[0].1.push((
        String::from("solvers::gramschmidt"),
        gramschmidt::bench::<100, 100>(f),
    ));
    res.inner[0]
        .1
        .push((String::from("solvers::lu"), lu::bench::<100>(f)));
    res.inner[0]
        .1
        .push((String::from("solvers::ludcmp"), ludcmp::bench::<100>(f)));
    res.inner[0]
        .1
        .push((String::from("solvers::trisolv"), trisolv::bench::<100>(f)));

    // Data mining.
    res.inner.push((String::from("Data mining"), Vec::new()));
    res.inner[1].1.push((
        String::from("correlation"),
        correlation::bench::<100, 100>(f),
    ));
    res.inner[1]
        .1
        .push((String::from("covariance"), covariance::bench::<100, 100>(f)));

    // medleys.
    res.inner.push((String::from("Medleys"), Vec::new()));

    res.inner[2]
        .1
        .push((String::from("deriche"), deriche::bench::<100, 100>(f)));
    res.inner[2].1.push((
        String::from("floyd_warshall"),
        floyd_warshall::bench::<100>(f),
    ));
    res.inner[2]
        .1
        .push((String::from("nussinov"), nussinov::bench::<100>(f)));

    // stencils.
    res.inner.push((String::from("Stencils"), Vec::new()));
    res.inner[3]
        .1
        .push((String::from("adi"), adi::bench::<100, 100>(f)));
    res.inner[3]
        .1
        .push((String::from("fdtd_2d"), fdtd_2d::bench::<100, 100, 100>(f)));
    res.inner[3]
        .1
        .push((String::from("heat_3d"), heat_3d::bench::<20, 100>(f)));
    res.inner[3]
        .1
        .push((String::from("jacobi_1d"), jacobi_1d::bench::<1000, 100>(f)));
    res.inner[3]
        .1
        .push((String::from("jacobi_2d"), jacobi_2d::bench::<100, 100>(f)));
    res.inner[3]
        .1
        .push((String::from("seidel_2d"), seidel_2d::bench::<100, 100>(f)));

    res
}
