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

pub struct SandboxInstance {
}

impl SandboxInstance {
	pub fn invoke(&self, _sandbox: &mut Sandbox, _export: &str) -> Result<(), Error> {
		panic!()
	}
}

pub struct Sandbox<'a> {
	phantom: ::core::marker::PhantomData<&'a ()>,
}

#[derive(Clone)]
pub struct Memory {
}

impl Memory {
	pub fn new(_initial: u32, _maximum: Option<u32>) -> Memory {
		panic!()
	}

	pub fn get(&self, _ptr: u32, _buf: &mut [u8]) {
		panic!()
	}
}

impl<'a> Sandbox<'a> {
	pub fn new() -> Sandbox<'a> {
		panic!()
	}

	pub fn register_closure<F: Fn(&[Value])>(&mut self, _module_name: &str, _field_name: &str, _f: &'a F) {
		panic!()
	}

	pub fn register_memory(&mut self, _module_name: &str, _field_name: &str, _memory: Memory) {
		panic!()
	}

	// TODO: Return `Result`
	pub fn instantiate(&mut self, _wasm: &[u8]) -> SandboxInstance {
		panic!()
	}
}
