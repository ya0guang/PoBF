use alloc::{boxed::Box, format, string::String, sync::Arc, vec::Vec};
use core::{
    error::Error,
    fmt::{Debug, Display},
    hash::Hash,
    sync::atomic::{AtomicBool, Ordering},
};
use hashbrown::HashMap;
use lazy_static::lazy_static;
use serde::{ser::SerializeMap, Deserialize, Serialize, Serializer};
use spin::RwLock;

pub type DbResult<T> = core::result::Result<T, DbError>;
pub type PersistentType<K, V> = Box<dyn Persistent<K, V>>;

pub const MINIMUM_OPERATION_LEN: usize = 2;

lazy_static! {
    /// A global singleton instance of the database.
    pub static ref SIMPLE_DATABASE: Arc<Database<String, String>> =
        Arc::new(Database::new_empty());

    /// A global file lock.
    pub static ref DB_FILELOCK: RwLock<()> = RwLock::new(());
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

/// A trait that represents all disk managers that deals with the disk operations.
///
/// This trait is designed to be `no_std` compatible and can reduce the codebase of
/// the kernel of our simple database.
pub trait Persistent<K, V>: Send + Sync
where
    K: Serialize + for<'a> Deserialize<'a>,
    V: Serialize + for<'a> Deserialize<'a>,
{
    /// Dumps the raw database to the disk.
    fn write_disk(&self, path: &str, buf: &[u8]) -> DbResult<()>;
    /// Loads the raw database from the disk.
    fn read_disk(&self, path: &str) -> DbResult<Vec<u8>>;
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
    /// An index: there is a lock on the database and another lock on the collection, but the
    /// granularity is not refined yet. This should be enough for our use case, though.
    /// The outer lock can be acquired easily using `read()`.
    inner: RwLock<HashMap<String, RwLock<HashMap<K, V>>>>,
    /// Indicates whether the database is ready for manipulation. The DBA must ensure that
    /// this field is properly initialized to `true`, or the database will wait forever using
    /// [`core::hint::spin_loop()`].
    ready: AtomicBool,
}

impl<K, V> Debug for Database<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Database")
            .field("inner", &self.inner.read())
            .field("ready", &self.ready)
            .finish()
    }
}

impl<K, V> Serialize for Database<K, V>
where
    K: Hash + Eq + Serialize,
    V: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let table = self.inner.read();
        let mut map = serializer.serialize_map(Some(table.len()))?;

        for (key, value) in table.iter() {
            // We need to use `&*` to explicitly tell serde that we are accessing the inner type, not
            // the `RwLockReadGuard`, which is treated as a smart pointer. The hashbrown::HashMap is
            // serializable, so we do not need to implement serialization.
            map.serialize_entry(key, &*value.read())?;
        }

        map.end()
    }
}

impl<K, V> Database<K, V> {
    /// Creates an empty database.
    pub fn new_empty() -> Self {
        Self {
            inner: RwLock::new(HashMap::new()),
            ready: AtomicBool::new(false),
        }
    }

    /// Explicitly makes the database to be ready for manipulations.
    pub fn make_ready(&self) {
        self.ready.store(true, Ordering::Release);
    }
}

impl<K, V> Database<K, V>
where
    K: Clone + Hash + PartialEq + PartialOrd + Ord + Eq + Debug,
    V: Clone,
{
    pub fn replace(&self, other: Self) {
        let mut lock = self.inner.write();
        lock.clear();
        // Consumes the other one.
        *lock = other.inner.into_inner();
        self.ready
            .store(other.ready.into_inner(), Ordering::Release);
    }

    /// Creates a new schema for this database. If the collection already exists, we overwrite it.
    pub fn make_schema(&self, schemas: &Vec<String>) -> DbResult<()> {
        schemas.iter().for_each(|collection| {
            self.inner
                .write()
                .insert(collection.clone(), RwLock::new(HashMap::new()));
        });

        Ok(())
    }

    /// Inserts a new key-value pair into the database; if this pair exists, returns false.
    pub fn insert(&self, collection: &str, key: K, value: V) -> DbResult<()> {
        if !self.ready.load(Ordering::Relaxed) {
            // Wait until the database is ok.
            core::hint::spin_loop();
        }

        match self.inner.read().get(collection) {
            Some(table) => {
                let mut lock = table.write();

                match lock.contains_key(&key) {
                    false => {
                        lock.insert(key, value);
                        Ok(())
                    }
                    true => Err(DbError::KeyRepeat(format!("{key:?}"))),
                }
            }

            None => Err(DbError::CollectionNotFound(collection.into())),
        }
    }

    /// Updates a key-value pair.
    pub fn update(&self, collection: &str, key: &K, value: V) -> DbResult<()> {
        if !self.ready.load(Ordering::Relaxed) {
            // Wait until the database is ok.
            core::hint::spin_loop();
        }

        let table = self.inner.read();
        let mut lock = table
            .get(collection)
            .ok_or(DbError::CollectionNotFound(collection.into()))?
            .write();
        let v = lock
            .get_mut(key)
            .ok_or(DbError::KeyNotFound(format!("{key:?}")))?;
        *v = value;
        Ok(())
    }

    /// Gets the key-value pair.
    pub fn get(&self, collection: &str, key: &K) -> DbResult<V> {
        if !self.ready.load(Ordering::Relaxed) {
            // Wait until the database is ok.
            core::hint::spin_loop();
        }

        self.inner
            .read()
            .get(collection)
            .ok_or(DbError::CollectionNotFound(collection.into()))?
            .read()
            .get(key)
            .cloned()
            .ok_or(DbError::KeyNotFound(format!("{:?}", key)))
    }

    /// Deletes a given key-pair from the database.
    pub fn delete(&self, collection: &str, key: &K) -> DbResult<V> {
        if !self.ready.load(Ordering::Relaxed) {
            // Wait until the database is ok.
            core::hint::spin_loop();
        }

        self.inner
            .read()
            .get(collection)
            .ok_or(DbError::CollectionNotFound(collection.into()))?
            .write()
            .remove(key)
            .ok_or(DbError::KeyNotFound(format!("{key:?}")))
    }
}

impl<K, V> Database<K, V>
where
    K: Hash + Eq + Serialize + for<'a> Deserialize<'a>,
    V: Serialize + for<'a> Deserialize<'a>,
{
    /// Dumps the content of the database to a given path using a persistent.
    pub fn dump(&self, path: &str, persistent: &PersistentType<K, V>) -> DbResult<()> {
        if !self.ready.load(Ordering::Relaxed) {
            // Wait until the database is ok.
            core::hint::spin_loop();
        }

        let contents = bincode::serialize(self).map_err(|_| DbError::SerializeError)?;
        DB_FILELOCK.write();
        persistent.write_disk(path, &contents)
    }

    /// Restores the database content from the disk.
    pub fn new_from_disk(path: &str, persistent: &PersistentType<K, V>) -> DbResult<Self> {
        let lock = DB_FILELOCK.read();
        let contents = persistent.read_disk(path)?;
        let hashmap = bincode::deserialize::<HashMap<String, HashMap<K, V>>>(contents.as_slice())
            .map_err(|_| DbError::SerializeError)?;
        drop(lock);

        let db = Self::new_empty();
        db.make_ready();

        // Load the contents.
        let mut lock = db.inner.write();
        for (k, v) in hashmap.into_iter() {
            lock.insert(k, RwLock::new(v));
        }
        drop(lock);

        Ok(db)
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
