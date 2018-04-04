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

use rstd::prelude::*;
use runtime_io::{print};

//

// #[repr(C)]
// union UntypedValue {
// 	as_i32: i32,
// 	as_i64: i64,
// 	as_f32: f32,
// 	as_f64: f64,
// }

// #[repr(C)]
// struct TaggedRawValue {
// 	tag: u32,
// 	untyped_value: UntypedValue,
// }

// impl TaggedRawValue {
// 	fn to_value(&self) -> Value {
// 		match self.tag {
// 			0 => Value::I32(
// 				unsafe {
// 					self.untyped_value.as_i32
// 				}
// 			),

// 			// TODO: Not yet implemented.
// 			_ => panic!(),
// 		}
// 	}
// }

#[repr(C)]
struct TaggedRawValue {
	value: i32,
}

impl TaggedRawValue {
	fn to_value(&self) -> Value {
		Value::I32(self.value)
	}
}

mod ffi {
	extern "C" {
		pub fn ext_sandbox_instantiate(
			unmarshal_thunk: extern "C" fn(ptr: *const super::TaggedRawValue, len: usize, f: fn(&[super::Value])),
			wasm_ptr: *const u8,
			wasm_len: usize,
			imports_ptr: *const u8,
			imports_len: usize,
		) -> u32;
		pub fn ext_sandbox_invoke(instance_id: u32, export_ptr: *const u8, export_len: usize) -> u32;
		pub fn ext_sandbox_memory_new(initial: u32, maximum: u32) -> u32;
		pub fn ext_sandbox_memory_get(memory_id: u32, offset: u32, buf_ptr: *mut u8, buf_len: usize);
		pub fn ext_sandbox_memory_set(memory_id: u32, offset: u32, val_ptr: *const u8, val_len: usize);

		// TODO: ext_instance_teardown
		// TODO: ext_memory_teardown
	}
}

#[derive(Clone)]
pub struct Memory {
	memory_id: u32,
}

impl Memory {
	pub fn new(initial: u32, maximum: Option<u32>) -> Memory {
		let memory_id = unsafe {
			let maximum = if let Some(maximum) = maximum {
				maximum
			} else {
				-1i32 as u32
			};
			ffi::ext_sandbox_memory_new(
				initial,
				maximum,
			)
		};
		Memory { memory_id }
	}

	pub fn get(&self, offset: u32, buf: &mut [u8]) {
		unsafe {
			ffi::ext_sandbox_memory_get(
				self.memory_id,
				offset,
				buf.as_mut_ptr(),
				buf.len(),
			)
		}
	}

	pub fn set(&self, offset: u32, val: &[u8]) {
		unsafe {
			ffi::ext_sandbox_memory_set(
				self.memory_id,
				offset,
				val.as_ptr(),
				val.len(),
			)
		}
	}
}

fn marshal_slice(slice: &[u8], out: &mut Vec<u8>) {
	// TODO: Lift the 255 limitation
	assert!(slice.len() <= 255);
	out.push(slice.len() as u8);
	out.extend_from_slice(slice);
}

fn marshal_imports(imports: &Imports) -> Vec<u8> {
	let mut result = Vec::new();
	let len = imports.map.len();
	print(len as u64);
	assert!(len <= 255);
	result.push(len as u8);
	for (&(ref module_name, ref field_name), externval) in &imports.map {
		marshal_slice(module_name, &mut result);
		marshal_slice(field_name, &mut result);

		match *externval {
			ExternVal::HostFunc(ref f) => {
				// id of HostFunc
				result.push(0);

				// TODO: Lift it
				let func_idx = *f as usize;
				assert!(func_idx <= 255);
				result.push(func_idx as u8);
			}
			ExternVal::Memory(ref m) => {
				// id of Memory
				result.push(1);

				assert!(m.memory_id <= 255);
				result.push(m.memory_id as u8);
			}
		}
	}
	result
}

struct InstanceImp {
	instance_id: u32,
}

extern "C" fn unmarshal_thunk(ptr: *const TaggedRawValue, len: usize, f: fn(&[Value])) {
	let raw_args = unsafe {
		if len == 0 {
			&[]
		} else {
			::core::slice::from_raw_parts(ptr, len)
		}
	};
	let args = raw_args.iter().map(|arg| arg.to_value()).collect::<Vec<_>>();
	f(&args)
}

impl InstanceImp {
	fn new(code: &[u8], imports: &Imports) -> InstanceImp {
		let imports = marshal_imports(imports);
		let instance_id = unsafe {
			ffi::ext_sandbox_instantiate(
				unmarshal_thunk,
				code.as_ptr(),
				code.len(),
				imports.as_ptr(),
				imports.len(),
			)
		};
		InstanceImp {
			instance_id,
		}
	}

	fn invoke(&mut self, name: &[u8], _args: &[Value]) -> Result<Option<Value>, Error> {
		// TODO: Args
		// TODO: Result
		let raw_result = unsafe {
			ffi::ext_sandbox_invoke(
				self.instance_id,
				name.as_ptr(),
				name.len(),
			)
		};
		if raw_result == 0 {
			Ok(None)
		} else {
			Err(Error::Trap)
		}
	}
}
