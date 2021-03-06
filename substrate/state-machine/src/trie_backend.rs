// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Trie-based state machine backend.

use std::collections::HashMap;
use std::sync::Arc;
use ethereum_types::H256 as TrieH256;
use hashdb::{DBValue, HashDB};
use kvdb::KeyValueDB;
use memorydb::MemoryDB;
use patricia_trie::{TrieDB, TrieDBMut, TrieError, Trie, TrieMut};
use {Backend};

/// Try convert into trie-based backend.
pub trait TryIntoTrieBackend {
	/// Try to convert self into trie backend.
	fn try_into_trie_backend(self) -> Option<TrieBackend>;
}

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
#[derive(Clone)]
pub struct TrieBackend {
	storage: TrieBackendStorage,
	root: TrieH256,
}

impl TrieBackend {
	/// Create new trie-based backend.
	pub fn with_kvdb(db: Arc<KeyValueDB>, storage_column: Option<u32>, root: TrieH256) -> Self {
		TrieBackend {
			storage: TrieBackendStorage::KeyValueDb(db, storage_column),
			root,
		}
	}

	/// Create new trie-based backend for genesis block.
	pub fn with_kvdb_for_genesis(db: Arc<KeyValueDB>, storage_column: Option<u32>) -> Self {
		let mut root = TrieH256::default();
		let mut mdb = MemoryDB::default();
		TrieDBMut::new(&mut mdb, &mut root);

		Self::with_kvdb(db, storage_column, root)
	}

	/// Create new trie-based backend backed by MemoryDb storage.
	pub fn with_memorydb(db: MemoryDB, root: TrieH256) -> Self {
		// TODO: check that root is a part of db???
		TrieBackend {
			storage: TrieBackendStorage::MemoryDb(db),
			root,
		}
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &TrieBackendStorage {
		&self.storage
	}

	/// Get trie root.
	pub fn root(&self) -> &TrieH256 {
		&self.root
	}
}

impl Backend for TrieBackend {
	type Error = String;
	type Transaction = MemoryDB;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let map_e = |e: Box<TrieError>| format!("Trie lookup error: {}", e);

		TrieDB::new(&eph, &self.root).map_err(map_e)?
			.get(key).map(|x| x.map(|val| val.to_vec())).map_err(map_e)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let collect_all = || -> Result<_, Box<TrieError>> {
			let trie = TrieDB::new(&eph, &self.root)?;
			let mut v = Vec::new();
			for x in trie.iter()? {
				let (key, value) = x?;
				v.push((key.to_vec(), value.to_vec()));
			}

			Ok(v)
		};

		match collect_all() {
			Ok(v) => v,
			Err(e) => {
				debug!(target: "trie", "Error extracting trie values: {}", e);
				Vec::new()
			}
		}
	}

	fn storage_root<I>(&self, delta: I) -> ([u8; 32], MemoryDB)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let mut write_overlay = MemoryDB::default();
		let mut root = self.root;
		{
			let mut eph = Ephemeral {
				storage: &self.storage,
				overlay: &mut write_overlay,
			};

			let mut trie = TrieDBMut::from_existing(&mut eph, &mut root).expect("prior state root to exist"); // TODO: handle gracefully
			for (key, change) in delta {
				let result = match change {
					Some(val) => trie.insert(&key, &val),
					None => trie.remove(&key), // TODO: archive mode
				};

				if let Err(e) = result {
					warn!(target: "trie", "Failed to write to trie: {}", e);
				}
			}
		}

		(root.0.into(), write_overlay)
	}
}

impl TryIntoTrieBackend for TrieBackend {
	fn try_into_trie_backend(self) -> Option<TrieBackend> {
		Some(self)
	}
}

pub struct Ephemeral<'a> {
	storage: &'a TrieBackendStorage,
	overlay: &'a mut MemoryDB,
}

impl<'a> Ephemeral<'a> {
	pub fn new(storage: &'a TrieBackendStorage, overlay: &'a mut MemoryDB) -> Self {
		Ephemeral {
			storage,
			overlay,
		}
	}
}

impl<'a> HashDB for Ephemeral<'a> {
	fn keys(&self) -> HashMap<TrieH256, i32> {
		self.overlay.keys() // TODO: iterate backing
	}

	fn get(&self, key: &TrieH256) -> Option<DBValue> {
		match self.overlay.raw(key) {
			Some((val, i)) => {
				if i <= 0 {
					None
				} else {
					Some(val)
				}
			}
			None => match self.storage.get(&key.0[..]) {
				Ok(x) => x,
				Err(e) => {
					warn!(target: "trie", "Failed to read from DB: {}", e);
					None
				},
			},
		}
	}

	fn contains(&self, key: &TrieH256) -> bool {
		self.get(key).is_some()
	}

	fn insert(&mut self, value: &[u8]) -> TrieH256 {
		self.overlay.insert(value)
	}

	fn emplace(&mut self, key: TrieH256, value: DBValue) {
		self.overlay.emplace(key, value)
	}

	fn remove(&mut self, key: &TrieH256) {
		self.overlay.remove(key)
	}
}

#[derive(Clone)]
pub enum TrieBackendStorage {
	/// Key value db + storage column.
	KeyValueDb(Arc<KeyValueDB>, Option<u32>),
	/// Hash db.
	MemoryDb(MemoryDB),
}

impl TrieBackendStorage {
	pub fn get(&self, key: &[u8]) -> Result<Option<DBValue>, String> {
		match *self {
			TrieBackendStorage::KeyValueDb(ref db, storage_column) =>
				db.get(storage_column, key)
					.map_err(|e| format!("Trie lookup error: {}", e)),
			TrieBackendStorage::MemoryDb(ref db) =>
				Ok(db.get(&TrieH256::from_slice(key))),
		}
	}
}

#[cfg(test)]
pub mod tests {
	use super::*;

	fn test_db() -> (MemoryDB, TrieH256) {
		let mut root = TrieH256::default();
		let mut mdb = MemoryDB::default();
		{
			let mut trie = TrieDBMut::new(&mut mdb, &mut root);
			trie.insert(b"key", b"value").unwrap();
			trie.insert(b"value1", &[42]).unwrap();
			trie.insert(b"value2", &[24]).unwrap();
			trie.insert(b":code", b"return 42").unwrap();
		}
		(mdb, root)
	}

	pub fn test_trie() -> TrieBackend {
		let (mdb, root) = test_db();
		TrieBackend::with_memorydb(mdb, root)
	}

	#[test]
	fn read_from_storage_returns_some() {
		assert_eq!(test_trie().storage(b"key").unwrap(), Some(b"value".to_vec()));
	}

	#[test]
	fn read_from_storage_returns_none() {
		assert_eq!(test_trie().storage(b"non-existing-key").unwrap(), None);
	}

	#[test]
	fn pairs_are_not_empty_on_non_empty_storage() {
		assert!(!test_trie().pairs().is_empty());
	}

	#[test]
	fn pairs_are_empty_on_empty_storage() {
		assert!(TrieBackend::with_memorydb(MemoryDB::new(), Default::default()).pairs().is_empty());
	}

	#[test]
	fn storage_root_is_non_default() {
		assert!(test_trie().storage_root(::std::iter::empty()).0 != [0; 32]);
	}

	#[test]
	fn storage_root_transaction_is_empty() {
		assert!(test_trie().storage_root(::std::iter::empty()).1.drain().is_empty());
	}

	#[test]
	fn storage_root_transaction_is_non_empty() {
		let (new_root, mut tx) = test_trie().storage_root(vec![(b"new-key".to_vec(), Some(b"new-value".to_vec()))]);
		assert!(!tx.drain().is_empty());
		assert!(new_root != test_trie().storage_root(::std::iter::empty()).0);
	}
}
