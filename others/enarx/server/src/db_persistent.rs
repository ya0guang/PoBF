use std::{
    io::{Read, Write},
    os::fd::FromRawFd,
    time,
};

use db::db::{DbError, DbResult, Persistent};
pub struct SgxPersistentLayer;

impl Persistent<String, String> for SgxPersistentLayer {
    fn write_disk(&self, path: &str, buf: &[u8]) -> DbResult<()> {
        println!("writing {path} with buf.len() = {} bytes", buf.len());

        let now = time::Instant::now();
        let mut file = unsafe { std::fs::File::from_raw_fd(4) };
        file.write_all(buf).map_err(|_| DbError::Unknown)?;
        let elapsed: time::Duration = now.elapsed();

        let throughput = (buf.len() as f64 / elapsed.as_secs_f64()) / 1000000.0;

        println!("[+] Time elapsed: {elapsed:?}; throughput: {throughput} MB/s");

        Ok(())
    }

    fn read_disk(&self, path: &str) -> DbResult<Vec<u8>> {
        println!("reading {path}");

        let now = time::Instant::now();
        let mut buf = vec![];
        unsafe { std::fs::File::from_raw_fd(4) }
            .read_to_end(&mut buf)
            .map_err(|_| DbError::PathNotFound(path.into()))?;
        let elapsed: time::Duration = now.elapsed();

        let throughput = (buf.len() as f64 / elapsed.as_secs_f64()) / 1000000.0;

        println!("[+] Time elapsed: {elapsed:?}; throughput: {throughput} MB/s");

        Ok(buf)
    }
}
