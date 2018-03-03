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

extern crate wasmi;
extern crate substrate_executor;


use substrate_executor::wasm_utils;
use std::collections::HashMap;
use std::mem;
use std::cell::RefCell;

use wasmi::TryInto;

use wasmi::{
	Externals, Module, ModuleInstance, ModuleRef, ModuleImportResolver, MemoryInstance,
	MemoryRef, Trap, TrapKind, ImportsBuilder, RuntimeArgs, RuntimeValue, Signature,
	GlobalDescriptor, MemoryDescriptor, TableDescriptor, TableRef, FuncRef, GlobalRef,
	ImportResolver, FuncInstance,
};
use wasmi::memory_units::{Pages};

#[derive(Debug)]
pub enum Error {
	Trap,
}

enum Void {}

#[derive(Debug)]
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

pub struct SandboxInstance {
	instance: ModuleRef,
}

impl SandboxInstance {
	pub fn invoke(&self, sandbox: &mut Sandbox, export: &str) -> Result<(), Error> {
		let result = self.instance.invoke_export(export, &[], sandbox);

		//
		match result {
			Ok(_) => Ok(()),
			Err(_err) => Err(Error::Trap),
		}
	}
}

enum TypedFuncPtr {
	Func0(fn()),
}

pub struct Sandbox<'a> {
	// TODO: Refactor
	wrappers: Vec<&'a Fn(&[Value])>,
	registered_funcs: HashMap<(String, String), usize>,
	memories: Vec<Memory>,
	registered_memories: HashMap<(String, String), usize>,
	memory: RefCell<Option<MemoryRef>>,
}

impl<'a> Externals for Sandbox<'a> {
	fn invoke_index(
		&mut self,
		index: usize,
		args: RuntimeArgs,
	) -> Result<Option<RuntimeValue>, Trap> {
		let args = args.as_ref().iter().map(|arg| match *arg {
			RuntimeValue::I32(v) => Value::I32(v),
			_ => panic!("Unsupported type!"),
		}).collect::<Vec<_>>();

		(self.wrappers[index])(&args);
		Ok(None)
	}
}

impl<'a> ImportResolver for Sandbox<'a> {
	fn resolve_func(
		&self,
		module_name: &str,
		field_name: &str,
		signature: &Signature,
	) -> Result<FuncRef, wasmi::Error> {
		let key = (module_name.to_string(), field_name.to_string());
		let idx = *self.registered_funcs.get(&key).ok_or_else(||
			wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
		)?;
		Ok(FuncInstance::alloc_host(signature.clone(), idx))
	}

	fn resolve_global(
		&self,
		_module_name: &str,
		_field_name: &str,
		_global_type: &GlobalDescriptor,
	) -> Result<GlobalRef, wasmi::Error> {
		// TODO:
		unimplemented!()
	}

	fn resolve_memory(
		&self,
		module_name: &str,
		field_name: &str,
		_memory_type: &MemoryDescriptor,
	) -> Result<MemoryRef, wasmi::Error> {
		let key = (module_name.to_string(), field_name.to_string());
		let idx = *self.registered_memories.get(&key).ok_or_else(||
			wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
		)?;
		Ok(self.memories[idx].memref.clone())
	}

	fn resolve_table(
		&self,
		_module_name: &str,
		_field_name: &str,
		_table_type: &TableDescriptor,
	) -> Result<TableRef, wasmi::Error> {
		// TODO:
		unimplemented!()
	}
}

#[derive(Clone)]
pub struct Memory {
	memref: MemoryRef,
}

impl Memory {
	pub fn new(initial: u32, maximum: Option<u32>) -> Memory {
		Memory {
			memref: MemoryInstance::alloc(Pages(initial as usize), maximum.map(|m| Pages(m as usize))).unwrap()
		}
	}

	pub fn get(&self, ptr: u32, buf: &mut [u8]) {
		self.memref.get_into(ptr, buf).unwrap();
	}
}

impl<'a> Sandbox<'a> {
	pub fn new() -> Sandbox<'a> {
		Sandbox {
			wrappers: Vec::new(),
			memories: Vec::new(),
			registered_funcs: HashMap::new(),
			registered_memories: HashMap::new(),
			memory: RefCell::new(None),
		}
	}

	// pub fn register_func0<R: wasm_utils::ConvertibleToWasm>(&mut self, module_name: &str, field_name: &str, f: fn() -> R) {
	// 	fn wrapper<R: wasm_utils::ConvertibleToWasm>(
	// 		f_raw: *const u8,
	// 		args: RuntimeArgs
	// 	) -> Result<Option<RuntimeValue>, Trap> {
	// 		use wasm_utils::ConvertibleToWasm;
	// 		unsafe {
	// 			let f = mem::transmute::<_, fn() -> R>(f_raw);
	// 			let result = f();
	// 			Ok(Some(result.to_runtime_value()))
	// 		}
	// 	}

	// 	let f_raw = unsafe {
	// 		mem::transmute::<_, *const u8>(f)
	// 	};
	// 	self.wrappers.push(WrappedFn {
	// 		wrapper: wrapper::<R>,
	// 		func: f_raw,
	// 	});
	// 	let f_idx = self.wrappers.len() - 1;

	// 	self.registered_funcs.insert((module_name.to_string(), field_name.to_string()), f_idx);
	// }

	// pub fn register_proc3(&mut self, module_name: &str, field_name: &str, f: fn(u32, u32, u32)) {
	// 	fn wrapper(
	// 		f_raw: *const u8,
	// 		args: RuntimeArgs
	// 	) -> Result<Option<RuntimeValue>, Trap>
	// 	{
	// 		let p1: u32 = args.as_ref()[0].try_into().unwrap();
	// 		let p2: u32 = args.as_ref()[1].try_into().unwrap();
	// 		let p3: u32 = args.as_ref()[2].try_into().unwrap();
	// 		unsafe {
	// 			let f = mem::transmute::<_, fn(u32, u32, u32)>(f_raw);
	// 			f(p1, p2, p3);
	// 			Ok(None)
	// 		}
	// 	}

	// 	let f_raw = unsafe {
	// 		mem::transmute::<_, *const u8>(f)
	// 	};
	// 	self.wrappers.push(WrappedFn {
	// 		wrapper: wrapper,
	// 		func: f_raw,
	// 	});
	// 	let f_idx = self.wrappers.len() - 1;

	// 	self.registered_funcs.insert((module_name.to_string(), field_name.to_string()), f_idx);
	// }

	pub fn register_closure<F: Fn(&[Value])>(&mut self, module_name: &str, field_name: &str, f: &'a F) {
		self.wrappers.push(f);
		let f_idx = self.wrappers.len() - 1;

		self.registered_funcs.insert((module_name.to_string(), field_name.to_string()), f_idx);
	}

	pub fn register_memory(&mut self, module_name: &str, field_name: &str, memory: Memory) {
		self.memories.push(memory);
		let mem_idx = self.memories.len() - 1;
		self.registered_memories.insert((module_name.to_string(), field_name.to_string()), mem_idx);
	}

	pub fn instantiate(&mut self, wasm: &[u8]) -> SandboxInstance {
		let module = Module::from_buffer(wasm).unwrap();
		let instance = ModuleInstance::new(
			&module,
			self
		).unwrap().assert_no_start();

		SandboxInstance {
			instance,
		}
	}
}
