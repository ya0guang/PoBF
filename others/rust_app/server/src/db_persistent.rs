use std::{io::Write, time};

use db::db::{DbError, DbResult, Persistent};
pub struct SgxPersistentLayer;

impl Persistent<String, String> for SgxPersistentLayer {
    fn write_disk(&self, path: &str, buf: &[u8]) -> DbResult<()> {
        println!("writing {path} with buf.len() = {} bytes", buf.len());

        let now = time::Instant::now();
        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .create(true)
            .open(path)
            .map_err(|_| DbError::PathNotFound(path.into()))?;
        file.write_all(buf).map_err(|_| DbError::Unknown)?;
        let elapsed: time::Duration = now.elapsed();

        let throughput = (buf.len() as f64 / elapsed.as_secs_f64()) / 1000000.0;

        println!("[+] Time elapsed: {elapsed:?}; throughput: {throughput} MB/s");

        Ok(())
    }

    fn read_disk(&self, path: &str) -> DbResult<Vec<u8>> {
        println!("reading {path}");

        let now = time::Instant::now();
        let buf = std::fs::read(path).map_err(|_| DbError::PathNotFound(path.into()))?;
        let elapsed: time::Duration = now.elapsed();

        let throughput = (buf.len() as f64 / elapsed.as_secs_f64()) / 1000000.0;

        println!("[+] Time elapsed: {elapsed:?}; throughput: {throughput} MB/s");

        Ok(buf)
    }
}
