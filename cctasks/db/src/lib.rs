//! A very simple Rust-written in-memory database that only supports the following operations:
//!
//! * insert,
//! * update
//! * search, and
//! * memory content dump.
//!
//! All these operations are performed via one interface.

#![cfg_attr(not(test), no_std)]
#![feature(error_in_core)]

extern crate alloc;

#[cfg(test)]
extern crate std;

use alloc::{format, string::String, vec::Vec};
use db::{parse_requests, Database, DumperType};
use spin::Once;

use crate::db::{DatabaseOperationType, SIMPLE_DATABASE};

pub mod db;

/// The PoCF platform should call `call_once` before the database can be used.
pub static DUMPER: Once<DumperType<String, String>> = Once::new();

/// Takes a batch of database operations and outputs the corresponding result.
///
/// # Note
///
/// The input format should be an array of database operations as follows.
///
/// ```txt
/// [id, type, key, value], [id, type, key, value], ...
/// ```
///
/// Example:
///
/// ```txt
/// '[0, 'read', 'foo', 'bar']; [1, 'read', 'baz', 'abc']'
/// ```
pub fn private_computation(input: Vec<u8>) -> Vec<u8> {
    // For simplicity, we assume the key value pair is string type.
    let requests = match parse_requests::<String, String>(input) {
        Ok(requests) => requests,
        Err(err) => return format!("{err}").into_bytes(),
    };

    let mut response = Vec::new();
    for request in requests {
        match request.operation {
            DatabaseOperationType::Insert(ref collection, key, value) => {
                match SIMPLE_DATABASE.write().insert(collection, key, value) {
                    Ok(_) => response.push(format!("#{:#<04x}: Insert OK", request.id)),
                    Err(err) => response.push(format!(
                        "#{:#<04x}: Insert failed because {}",
                        request.id, err
                    )),
                }
            }
            DatabaseOperationType::Read(ref collection, ref key) => {
                match SIMPLE_DATABASE.read().get(collection, key) {
                    Ok(value) => response.push(format!(
                        "#{:#<04x}: Read OK, value is `{}`",
                        request.id, value
                    )),
                    Err(err) => response.push(format!(
                        "#{:#<04x}: Read failed because {}",
                        request.id, err
                    )),
                }
            }
            DatabaseOperationType::Update(ref collection, ref key, value) => {
                match SIMPLE_DATABASE.write().update(collection, key, value) {
                    Ok(_) => response.push(format!("#{:#<04x}: Update OK", request.id)),
                    Err(err) => response.push(format!(
                        "#{:#<04x}: Update failed because {}",
                        request.id, err
                    )),
                }
            }
            DatabaseOperationType::Load(ref path) => {
                if DUMPER.get().is_none() {
                    response.push(format!(
                        "#{:#<04x}: Load failed because dumper is empty ",
                        request.id,
                    ))
                }

                let db = match Database::new_from_disk(path, DUMPER.get().unwrap()) {
                    // Abort on load failure.
                    Err(err) => return format!("{err}").into_bytes(),
                    Ok(db) => db,
                };

                *SIMPLE_DATABASE.write() = db;
                response.push(format!("#{:#<04x}: Load OK", request.id));
            }
            DatabaseOperationType::Dump(ref path) => {
                if DUMPER.get().is_none() {
                    response.push(format!(
                        "#{:#<04x}: Dump failed because dumper is empty ",
                        request.id,
                    ))
                }

                match SIMPLE_DATABASE.write().dump(path, DUMPER.get().unwrap()) {
                    Ok(_) => response.push(format!("#{:#<04x}: Dump OK", request.id)),
                    Err(err) => response.push(format!(
                        "#{:#<04x}: Dump failed because {}",
                        request.id, err
                    )),
                }
            }
            ty => response.push(format!("#{:#<04x}: Unsupported type {:?}", request.id, ty)),
        }

        response.push("\n".into());
    }

    response
        .into_iter()
        .map(|res| res.as_bytes().to_vec())
        .flatten()
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;
    use hashbrown::HashMap;

    struct PersistentLayer;

    unsafe impl Sync for PersistentLayer {}
    unsafe impl Send for PersistentLayer {}

    impl db::Persistent<String, String> for PersistentLayer {
        fn dump(&self, db: &db::Database<String, String>, path: &str) -> db::DbResult<()> {
            let contents =
                bincode::serialize(db.get_inner()).map_err(|_| db::DbError::SerializeError)?;
            std::fs::write(path, contents).map_err(|_| db::DbError::PathNotFound("dir".into()))
        }

        fn load(&self, path: &str) -> db::DbResult<HashMap<String, HashMap<String, String>>> {
            let bytes = std::fs::read(path).map_err(|_| db::DbError::PathNotFound(path.into()))?;
            bincode::deserialize(bytes.as_slice()).map_err(|_| db::DbError::SerializeError)
        }
    }

    #[test]
    fn test_create_empty_db() {
        let _db = db::Database::<String, String>::new_empty();
    }

    #[test]
    fn test_parse_requests() {
        let requests = "[0, read, field0, foo]; [2, update, field0, marry, me]; [3, scan, field0, abc, 29]; [4, dump, /usr/bin/]; [5, load, /usr/bin]";
        let result = db::parse_requests::<String, String>(requests.as_bytes().to_vec());
        assert!(result.is_ok(), "not ok {result:?}");

        let requests = "[0, read, field0, foo]; [1, read, field0, baz]; [2, update,field0, marry, me]; [3, scan, abc, aa]";
        let result = db::parse_requests::<String, String>(requests.as_bytes().to_vec());
        assert!(result.is_err(), "not error {result:?}");
    }

    #[test]
    fn test_transaction() {
        let schemas = ["field0".to_string()].to_vec();
        let requests =
            "[0, insert, field0, foo, bar]; [1, read, field0, foo]; [2, update, field0, foo, baz]";

        let mut lock = SIMPLE_DATABASE.write();
        lock.make_schema(&schemas).unwrap();
        lock.make_ready();
        drop(lock);

        let response = private_computation(requests.as_bytes().to_vec());
        println!("{}", String::from_utf8(response).unwrap());
    }

    #[test]
    fn test_dump() {
        let schemas = ["field0".to_string()].to_vec();
        let requests =
            "[0, insert, field0, foo, bar]; [1, read, field0, foo]; [2, update, field0, foo, baz]";

        let mut lock = SIMPLE_DATABASE.write();
        lock.make_schema(&schemas).unwrap();
        lock.make_ready();
        drop(lock);

        private_computation(requests.as_bytes().to_vec());
        let persistent_layer: Box<dyn db::Persistent<String, String>> = Box::new(PersistentLayer);
        SIMPLE_DATABASE
            .read()
            .dump("./dump.bin", &persistent_layer)
            .unwrap();
    }

    #[test]
    fn test_load() {
        let persistent_layer: Box<dyn db::Persistent<String, String>> = Box::new(PersistentLayer);
        let db = db::Database::new_from_disk("./dump.bin", &persistent_layer).unwrap();

        println!("{:#?}", db.get_inner());
    }
}
