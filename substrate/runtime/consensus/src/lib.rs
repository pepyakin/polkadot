// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Conensus module for runtime; manages the authority set ready for the native code.

#![cfg_attr(not(feature = "std"), no_std)]

#[allow(unused_imports)] #[macro_use] extern crate substrate_runtime_std as rstd;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;

#[cfg(feature = "std")] #[macro_use] extern crate serde_derive;
#[cfg(feature = "std")] extern crate serde;

use rstd::prelude::*;
use runtime_support::storage;
use runtime_support::storage::unhashed::StorageVec;

pub const AUTHORITY_AT: &'static[u8] = b":auth:";
pub const AUTHORITY_COUNT: &'static[u8] = b":auth:len";

struct AuthorityStorageVec<S: codec::Slicable + Default>(rstd::marker::PhantomData<S>);
impl<S: codec::Slicable + Default> StorageVec for AuthorityStorageVec<S> {
	type Item = S;
	const PREFIX: &'static[u8] = AUTHORITY_AT;
}

pub const CODE: &'static[u8] = b":code";

pub trait Trait: PartialEq + Eq + Clone {
	type SessionKey: codec::Slicable + Default;
	type PrivAux;
}

decl_module! {
	trait Trait as T;
	pub struct Module;
	pub enum PrivCall where aux: T::PrivAux {
		fn set_code(aux, new: Vec<u8>) = 0;
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities. These are the session keys.
	pub fn authorities() -> Vec<T::SessionKey> {
		AuthorityStorageVec::<T::SessionKey>::items()
	}

	/// Set the new code.
	fn set_code(_aux: &T::PrivAux, new: Vec<u8>) {
		Internal::<T>::set_code(new);
	}
}

pub struct Internal<T: Trait>(rstd::marker::PhantomData<T>);

impl<T: Trait> Internal<T> {
	/// Set the new code.
	pub fn set_code(new: Vec<u8>) {
		storage::unhashed::put_raw(CODE, &new);
	}

	/// Set the current set of authorities' session keys.
	///
	/// Called by `next_session` only.
	pub fn set_authorities(authorities: &[T::SessionKey]) {
		AuthorityStorageVec::<T::SessionKey>::set_items(authorities);
	}

	/// Set a single authority by index.
	pub fn set_authority(index: u32, key: &T::SessionKey) {
		AuthorityStorageVec::<T::SessionKey>::set_item(index, key);
	}
}