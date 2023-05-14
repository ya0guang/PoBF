use alloc::{boxed::Box, format, string::String, vec::Vec};
use core::{
    error::Error,
    fmt::{Debug, Display},
    hash::Hash,
};
use hashbrown::HashMap;
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
use spin::RwLock;

pub type DbResult<T> = core::result::Result<T, DbError>;
pub type DumperType<K, V> = Box<dyn Persistent<K, V>>;

pub const MINIMUM_OPERATION_LEN: usize = 2;

lazy_static! {
    /// A global singleton instance of the database.
    pub static ref SIMPLE_DATABASE: RwLock<Database<String, String>> =
        RwLock::new(Database::new_empty());
}

pub enum DbError {
    ParseError,
    InvalidOperation(String),
    KeyNotFound(String),
    CollectionNotFound(String),
    KeyRepeat(String),
    PathNotFound(String),
    DbNotReady,
    SerializeError,
    Unknown,
}

impl Error for DbError {}

impl Debug for DbError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ParseError => write!(f, "Parser reported an error. Maybe the input is invalid"),
            Self::InvalidOperation(op) => {
                write!(f, "The operation type {op} is invalid or unimplemented yet")
            }
            Self::KeyRepeat(key) => write!(f, "{key} was found duplicate in the database"),
            Self::KeyNotFound(key) => write!(f, "{key} was not found in the database"),
            Self::CollectionNotFound(collection) => {
                write!(f, "The requested collection {collection:?} does not exist")
            }
            Self::PathNotFound(path) => write!(f, "{path} does not exist"),
            Self::DbNotReady => write!(f, "Database not ready"),
            Self::SerializeError => write!(f, "Cannot serialize or deserialize the database"),
            Self::Unknown => write!(f, "Unknown error"),
        }
    }
}

impl Display for DbError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Debug::fmt(&self, f)
    }
}

/// A trait that represents all disk managers that deals with the disk operations. Making this
/// a generic trait has the following benefits:
///
/// * The codebase of the in-memory database will be decreased.
/// * The implementation of the persistent can be platform-specific.
pub trait Persistent<K, V>: Send + Sync
where
    K: Clone + Hash + Serialize + for<'a> Deserialize<'a>,
    V: Clone + Serialize + for<'a> Deserialize<'a>,
{
    /// Dumps the database onto the disk.
    fn dump(&self, db: &Database<K, V>, path: &str) -> DbResult<()>;
    /// Loads teh database from the disk.
    fn load(&self, path: &str) -> DbResult<HashMap<String, HashMap<K, V>>>;
}

pub trait AsBytes {
    fn to_bytes(&self) -> Vec<u8>;
    fn from_bytes(bytes: &[u8]) -> Self;
}

impl AsBytes for String {
    fn from_bytes(bytes: &[u8]) -> Self {
        Self::from_utf8(bytes.to_vec()).unwrap()
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.as_bytes().to_vec()
    }
}

#[derive(Debug)]
pub struct DatabaseOperation<K, V>
where
    K: Clone + Hash + PartialEq + PartialOrd + Ord + Eq + Debug,
{
    pub id: usize,
    pub operation: DatabaseOperationType<K, V>,
}

#[derive(Debug)]
pub enum DatabaseOperationType<K, V>
where
    K: Clone + Hash + PartialEq + PartialOrd + Ord + Eq + Debug,
{
    Update(String, K, V),
    Read(String, K),
    Insert(String, K, V),
    /// Scans over the index with a given starting key and the number of keys to be scanned.
    Scan(String, K, usize),
    /// Loads the content.
    Load(String),
    /// Dumps the database.
    Dump(String),
}

pub struct Database<K, V> {
    /// An index.
    inner: HashMap<String, HashMap<K, V>>,
    ready: bool,
}

impl<K, V> Database<K, V>
where
    K: Clone + Hash + PartialEq + PartialOrd + Ord + Eq + Debug,
    V: Clone,
{
    /// Creates an empty database.
    pub fn new_empty() -> Self {
        Self {
            inner: HashMap::new(),
            ready: false,
        }
    }

    /// Reveals the inner content.
    pub fn get_inner(&self) -> &HashMap<String, HashMap<K, V>> {
        &self.inner
    }

    /// Creates a new schema for this database. If the collection already exists, we overwrite it.
    pub fn make_schema(&mut self, schemas: &Vec<String>) -> DbResult<()> {
        schemas.iter().for_each(|collection| {
            self.inner.insert(collection.clone(), HashMap::new());
        });

        Ok(())
    }

    /// Explicitly makes the database to be ready for manipulations.
    pub fn make_ready(&mut self) {
        self.ready = true;
    }

    /// Inserts a new key-value pair into the database; if this pair exists, returns false.
    pub fn insert(&mut self, collection: &str, key: K, value: V) -> DbResult<()> {
        if !self.ready {
            return Err(DbError::DbNotReady);
        }

        match self.inner.get_mut(collection) {
            Some(table) => match table.contains_key(&key) {
                false => {
                    table.insert(key, value);
                    Ok(())
                }
                true => Err(DbError::KeyRepeat(format!("{key:?}"))),
            },

            None => Err(DbError::CollectionNotFound(collection.into())),
        }
    }

    /// Updates a key-value pair.
    pub fn update(&mut self, collection: &str, key: &K, value: V) -> DbResult<()> {
        if !self.ready {
            return Err(DbError::DbNotReady);
        }

        let v = self
            .inner
            .get_mut(collection)
            .ok_or(DbError::CollectionNotFound(collection.into()))?
            .get_mut(key)
            .ok_or(DbError::KeyNotFound(format!("{key:?}")))?;
        *v = value;
        Ok(())
    }

    /// Gets the key-value pair.
    pub fn get(&self, collection: &str, key: &K) -> DbResult<V> {
        if !self.ready {
            return Err(DbError::DbNotReady);
        }

        self.inner
            .get(collection)
            .ok_or(DbError::CollectionNotFound(collection.into()))?
            .get(key)
            .cloned()
            .ok_or(DbError::KeyNotFound(format!("{:?}", key)))
    }

    /// Deletes a given key-pair from the database.
    pub fn delete(&mut self, collection: &str, key: &K) -> DbResult<V> {
        if !self.ready {
            return Err(DbError::DbNotReady);
        }

        self.inner
            .get_mut(collection)
            .ok_or(DbError::CollectionNotFound(collection.into()))?
            .remove(key)
            .ok_or(DbError::KeyNotFound(format!("{key:?}")))
    }
}

impl<K, V> Database<K, V>
where
    K: Clone + Hash + PartialEq + PartialOrd + Ord + Eq + Serialize + for<'a> Deserialize<'a>,
    V: Clone + Serialize + for<'a> Deserialize<'a>,
{
    /// Dumps the content of the database to a given path using a persistent.
    pub fn dump(&self, path: &str, persistent: &DumperType<K, V>) -> DbResult<()> {
        if !self.ready {
            return Err(DbError::DbNotReady);
        }

        persistent.dump(self, path)
    }

    /// Restores the database content from the disk.
    pub fn new_from_disk(path: &str, persistent: &DumperType<K, V>) -> DbResult<Self> {
        let inner = persistent.load(path)?;

        Ok(Self { inner, ready: true })
    }
}

/// Given a byte array that represents the ut8 encoded string to a vector of database requests. The result
/// can then be used to perform the corresponding operation via `private_computation`.
pub fn parse_requests<K, V>(requests: Vec<u8>) -> DbResult<Vec<DatabaseOperation<K, V>>>
where
    K: Clone + Hash + PartialEq + PartialOrd + Ord + Eq + Debug + AsBytes,
    V: AsBytes,
{
    let requests = String::from_utf8(requests)
        .map_err(|_| DbError::ParseError)?
        .split_whitespace()
        .collect::<String>();

    let mut parsed_requests = Vec::new();
    for item in requests.split(";") {
        let inner_items = item[1..item.len() - 1].split(",").collect::<Vec<_>>();

        // The request is mal-formed.
        if inner_items.len() < MINIMUM_OPERATION_LEN {
            return Err(DbError::ParseError);
        }

        let id = inner_items[0]
            .parse::<usize>()
            .map_err(|_| DbError::ParseError)?;

        match inner_items[1].to_ascii_lowercase().as_str() {
            "insert" => {
                if inner_items.len() != 5 {
                    return Err(DbError::ParseError);
                }

                parsed_requests.push(DatabaseOperation {
                    id,
                    operation: DatabaseOperationType::Insert(
                        inner_items[2].into(),
                        K::from_bytes(inner_items[3].as_bytes()),
                        V::from_bytes(inner_items[4].as_bytes()),
                    ),
                })
            }
            "read" => {
                if inner_items.len() != 4 {
                    return Err(DbError::ParseError);
                }

                parsed_requests.push(DatabaseOperation {
                    id,
                    operation: DatabaseOperationType::Read(
                        inner_items[2].into(),
                        K::from_bytes(inner_items[3].as_bytes()),
                    ),
                })
            }
            "update" => {
                if inner_items.len() != 5 {
                    return Err(DbError::ParseError);
                }

                parsed_requests.push(DatabaseOperation {
                    id,
                    operation: DatabaseOperationType::Update(
                        inner_items[2].into(),
                        K::from_bytes(inner_items[3].as_bytes()),
                        V::from_bytes(inner_items[4].as_bytes()),
                    ),
                })
            }
            "scan" => {
                if inner_items.len() != 5 {
                    return Err(DbError::ParseError);
                }

                parsed_requests.push(DatabaseOperation {
                    id,
                    operation: DatabaseOperationType::Scan(
                        inner_items[2].into(),
                        K::from_bytes(inner_items[3].as_bytes()),
                        inner_items[4].parse().map_err(|_| DbError::ParseError)?,
                    ),
                })
            }

            "init" => todo!(),
            "load" => {
                if inner_items.len() != 3 {
                    return Err(DbError::ParseError);
                }

                parsed_requests.push(DatabaseOperation {
                    id,
                    operation: DatabaseOperationType::Load(inner_items[2].into()),
                })
            }
            "dump" => {
                if inner_items.len() != 3 {
                    return Err(DbError::ParseError);
                }

                parsed_requests.push(DatabaseOperation {
                    id,
                    operation: DatabaseOperationType::Dump(inner_items[2].into()),
                })
            }

            op => return Err(DbError::InvalidOperation(op.into())),
        }
    }

    Ok(parsed_requests)
}
