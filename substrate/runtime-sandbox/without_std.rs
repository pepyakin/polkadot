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
		pub fn ext_sandbox_new() -> u32;
		pub fn ext_sandbox_instantiate(sandbox_id: u32, wasm_ptr: *const u8, wasm_len: usize) -> u32;
		pub fn ext_sandbox_invoke(sandbox_id: u32, instance_id: u32, export_ptr: *const u8, export_len: usize) -> u32;
		pub fn ext_sandbox_register_closure(
			sandbox_id: u32,
			module_name_ptr: *const u8,
			module_name_len: usize,
			field_name_ptr: *const u8,
			field_name_len: usize,
			user_data: *const u8,
			fn_ptr: extern "C" fn(*const u8, *const super::TaggedRawValue, usize),
		);
		pub fn ext_sandbox_register_memory(
			sandbox_id: u32,
			module_name_ptr: *const u8,
			module_name_len: usize,
			field_name_ptr: *const u8,
			field_name_len: usize,
			memory_id: u32,
		);
		pub fn ext_sandbox_memory_new(initial: u32, maximum: u32) -> u32;
		pub fn ext_sandbox_memory_get(memory_id: u32, offset: u32, buf_ptr: *mut u8, buf_len: usize);
		pub fn ext_sandbox_memory_set(memory_id: u32, offset: u32, val_ptr: *const u8, val_len: usize);

		// TODO: ext_sandbox_teardown
	}
}

enum Void {}

pub struct SandboxInstance {
	instance_id: u32,
}

impl SandboxInstance {
	pub fn invoke(&self, sandbox: &mut Sandbox, export: &str) -> Result<(), Error> {
		let raw_result = unsafe {
			ffi::ext_sandbox_invoke(
				sandbox.sandbox_id,
				self.instance_id,
				export.as_ptr(),
				export.len(),
			)
		};
		if raw_result == 0 {
			Ok(())
		} else {
			Err(Error::Trap)
		}
	}
}

pub struct Sandbox<'a> {
	sandbox_id: u32,
	phantom: ::core::marker::PhantomData<&'a ()>,
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

impl<'a> Sandbox<'a> {
	pub fn new() -> Sandbox<'a> {
		let sandbox_id = unsafe {
			ffi::ext_sandbox_new()
		};
		Sandbox {
			sandbox_id,
			phantom: ::core::marker::PhantomData,
		}
	}

	pub fn register_closure<F: Fn(&[Value])>(&mut self, module_name: &str, field_name: &str, f: &'a F) {
		extern "C" fn wrapper<F>(user_data: *const u8, args_ptr: *const TaggedRawValue, args_len: usize)
		where
			F: Fn(&[Value]),
		{
			print(::core::mem::size_of::<TaggedRawValue>() as u64);

			unsafe {
				print(1338);
				print(::core::slice::from_raw_parts(args_ptr as *const u8, ::core::mem::size_of::<TaggedRawValue>() * args_len));
			}

			let opt_closure = user_data as *const Option<F> as *mut Option<F>;
			unsafe {
				let args = if args_len == 0 {
					&[]
				} else {
					::core::slice::from_raw_parts(args_ptr, args_len)
				};
				let args: Vec<_> = args.iter().map(|arg| {
					let v = arg.to_value();
					print(1339);
					// print(arg.tag as u64);
					// print(arg.untyped_value.as_i32 as u64);
					print(arg.value as u64);
					print(v.as_i32() as u64);
					v
				}).collect::<Vec<_>>();
				(*opt_closure).take().unwrap()(&args)
			}
		}

		let closure_data = f as *const _ as *mut u8;

		unsafe {
			ffi::ext_sandbox_register_closure(
				self.sandbox_id,
				module_name.as_ptr(),
				module_name.len(),
				field_name.as_ptr(),
				field_name.len(),
				closure_data,
				wrapper::<F>,
			)
		}
	}

	pub fn register_memory(&mut self, module_name: &str, field_name: &str, memory: Memory) {
		unsafe {
			ffi::ext_sandbox_register_memory(
				self.sandbox_id,
				module_name.as_ptr(),
				module_name.len(),
				field_name.as_ptr(),
				field_name.len(),
				memory.memory_id,
			);
		}
	}

	// TODO: Return `Result`
	pub fn instantiate(&mut self, wasm: &[u8]) -> SandboxInstance {
		let instance_id = unsafe {
			ffi::ext_sandbox_instantiate(
				self.sandbox_id,
				wasm.as_ptr(),
				wasm.len(),
			)
		};
		SandboxInstance {
			instance_id,
		}
	}
}
