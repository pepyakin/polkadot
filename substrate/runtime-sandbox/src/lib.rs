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

//! This library contains sandboxing primitives.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(lang_items))]
#![cfg_attr(not(feature = "std"), feature(core_intrinsics))]
#![cfg_attr(not(feature = "std"), feature(alloc))]

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;

use rstd::collections::btree_map::BTreeMap;

#[cfg(feature = "std")]
include!("../with_std.rs");

#[cfg(not(feature = "std"))]
include!("../without_std.rs");

#[cfg_attr(feature = "std", derive(Debug))]
pub enum Error {
	Trap,
}

#[cfg_attr(feature = "std", derive(Debug))]
pub enum Value {
	I32(i32),
}

impl Value {
	pub fn as_i32(&self) -> i32 {
		match *self {
			Value::I32(v) => v,
		}
	}
}

enum ExternVal {
	// This could be used for dynamic-linking implementation.
	// However, FuncRef would be more useful?
	HostFunc(fn(&[Value])),

	// `Memory` or `MemoryId`? This implies that `Memory` should be cloneable, since
	// it would require to have atleast two references (one for imports and one for manipulation
	// from the environment)
	Memory(Memory),

	// TODO: Globals?
	// TODO: Tables?
}

pub struct Imports {
	map: BTreeMap<(Vec<u8>, Vec<u8>), ExternVal>,
}

impl Imports {
	pub fn new() -> Imports {
		Imports {
			map: BTreeMap::new(),
		}
	}

	pub fn add_host_func<N1, N2>(&mut self, module: N1, field: N2, f: fn(&[Value]))
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		self.map.insert((module.into(), field.into()), ExternVal::HostFunc(f));
	}

	pub fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		self.map.insert((module.into(), field.into()), ExternVal::Memory(mem));
	}
}

pub struct Instance {
	inner: InstanceImp,
}

impl Instance {
	// TODO: Create a special structure for code for caching?
	pub fn new(code: &[u8], imports: &Imports) -> Instance {
		Instance {
			inner: InstanceImp::new(code, imports),
		}
	}

	// TODO: Names can only be a proper utf8.
	pub fn invoke(&mut self, name: &[u8], args: &[Value]) -> Result<Option<Value>, Error> {
		self.inner.invoke(name, args)
	}
}
