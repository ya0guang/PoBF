use core::time::Duration;

use alloc::{string::String, vec, vec::Vec};
use db::db::{DbError, DbResult, Persistent};
use sgx_tseal::seal::*;
use sgx_types::error::SgxStatus;

use crate::{
    log,
    networking_utils::unix_time,
    ocall::{ocall_get_file_size, ocall_read_data, ocall_write_data},
    ocall_log, ocall_write_data_prologue, verified_log,
};

const BATCH: u64 = 1 << 24;

type SecretTaint = ();

pub struct SgxPersistentLayer;

impl Persistent<String, String> for SgxPersistentLayer {
    fn write_disk(&self, path: &str, buf: &[u8]) -> DbResult<()> {
        verified_log!(SecretTaint, "[+] Writing {} bytes", buf.len());
        let mut ret_val = SgxStatus::Success;
        unsafe {
            ocall_write_data_prologue(&mut ret_val, path.as_ptr(), path.len() as _);
        }

        // Seal the data using the platform key.
        let begin = unix_time(3).map_err(|_| DbError::Unknown)?;
        let buf = SealedData::<[u8]>::seal(buf, None)
            .map_err(|_| DbError::Unknown)?
            .into_bytes()
            .map_err(|_| DbError::Unknown)?;
        let file_size = buf.len() as u64;

        let batch_num = if file_size % BATCH != 0 {
            file_size / BATCH + 1
        } else {
            file_size / BATCH
        };

        for i in 0..batch_num {
            let mut write_size = BATCH.min(file_size as u64 - i * BATCH);

            let mut ret_val = SgxStatus::Success;
            let res = unsafe {
                ocall_write_data(
                    &mut ret_val,
                    path.as_ptr(),
                    path.len() as _,
                    buf.as_ptr().add((i * BATCH) as usize),
                    write_size as _,
                )
            };

            if res != SgxStatus::Success {
                return Err(DbError::Unknown);
            }
        }
        let end = unix_time(3).map_err(|_| DbError::Unknown)?;

        let elapsed = Duration::from_nanos(end - begin);
        let throughput = (buf.len() as f64 / elapsed.as_secs_f64()) / 1000000.0;
        verified_log!(
            SecretTaint,
            "[+] Time elapsed: {:?}; throughput: {} MB/s",
            elapsed,
            throughput,
        );

        Ok(())
    }

    fn read_disk(&self, path: &str) -> DbResult<Vec<u8>> {
        // Get the file size of the database snapshot.
        let mut file_size = 0u64;
        let mut ret_val = SgxStatus::Success;
        let res = unsafe {
            ocall_get_file_size(&mut ret_val, path.as_ptr(), path.len() as _, &mut file_size)
        };
        if res != SgxStatus::Success {
            return Err(DbError::PathNotFound(path.into()));
        }

        verified_log!(SecretTaint, "[+] Reading {} bytes", file_size);

        let batch_num = if file_size % BATCH != 0 {
            file_size / BATCH + 1
        } else {
            file_size / BATCH
        };

        let mut content = vec![0u8; file_size as usize];
        let begin = unix_time(3).map_err(|_| DbError::Unknown)?;
        for i in 0..batch_num {
            let mut read_size = BATCH.min(content.len() as u64 - i * BATCH);

            let res = unsafe {
                ocall_read_data(
                    &mut ret_val,
                    path.as_ptr(),
                    path.len() as _,
                    (i * BATCH) as u64,
                    content.as_mut_ptr().add((i * BATCH) as usize),
                    read_size as _,
                    &mut (read_size as _),
                )
            };

            if res != SgxStatus::Success {
                return Err(DbError::Unknown);
            }
        }

        // Unseal the data.
        let content = UnsealedData::<[u8]>::unseal_from_bytes(content)
            .map_err(|e| {
                verified_log!(SecretTaint, "{}", e);
                DbError::SerializeError
            })?
            .into_plaintext()
            .to_vec();
        let end = unix_time(3).map_err(|_| DbError::Unknown)?;

        let elapsed = Duration::from_nanos(end - begin);
        let throughput = (file_size as f64 / elapsed.as_secs_f64()) / 1000000.0;
        verified_log!(
            SecretTaint,
            "[+] Time elapsed: {:?}; throughput: {} MB/s",
            elapsed,
            throughput,
        );

        Ok(content)
    }
}
