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

use std::collections::HashMap;

use wasmi::{
	Externals, Module, ModuleInstance, ModuleRef, MemoryInstance,
	MemoryRef, Trap, RuntimeArgs, RuntimeValue, Signature,
	GlobalDescriptor, MemoryDescriptor, TableDescriptor, TableRef, FuncRef, GlobalRef,
	ImportResolver, FuncInstance,
};
use wasmi::memory_units::{Pages};

///

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

	pub fn set(&self, ptr: u32, value: &[u8]) {
		self.memref.set(ptr, value).unwrap();
	}
}

struct ImportsExternals {
	funcs: Vec<fn(&[Value])>,
}
impl Externals for ImportsExternals {
	fn invoke_index(
		&mut self,
		index: usize,
		args: RuntimeArgs,
	) -> Result<Option<RuntimeValue>, Trap> {
		let args = args.as_ref().iter().map(|arg| match *arg {
			RuntimeValue::I32(v) => Value::I32(v),
			_ => panic!("Unsupported type!"),
		}).collect::<Vec<_>>();

		(self.funcs[index])(&args);
		Ok(None)
	}
}

struct ImportsAdapter<'a> {
	// We can't point to FuncRef, since it's requires a function signature and
	// we don't yet know it.
	func_map: HashMap<(Vec<u8>, Vec<u8>), usize>,
	imports: &'a Imports,
	externals: ImportsExternals,
}
impl<'a> ImportsAdapter<'a> {
	fn new(imports: &'a Imports) -> ImportsAdapter<'a> {
		// Convert slice of imports into a Map of functions.
		let mut externals = ImportsExternals {
			funcs: Vec::new(),
		};
		let mut func_map = HashMap::new();
		for (&(ref module_name, ref field_name), externval) in &imports.map {
			if let ExternVal::HostFunc(ref f) = *externval {
				let k = (module_name.to_owned(), field_name.to_owned());
				let idx = externals.funcs.len();
				externals.funcs.push(*f);
				func_map.insert(k, idx);
			}
		}
		ImportsAdapter {
			func_map,
			imports,
			externals,
		}
	}
	fn into_externals(self) -> ImportsExternals {
		self.externals
	}
}
impl<'a> ImportResolver for ImportsAdapter<'a> {
	fn resolve_func(
		&self,
		module_name: &str,
		field_name: &str,
		signature: &Signature,
	) -> Result<FuncRef, wasmi::Error> {
		let key = (module_name.as_bytes().to_owned(), field_name.as_bytes().to_owned());
		let func_idx = self.func_map.get(&key).ok_or_else(||
			wasmi::Error::Instantiation(
				format!("Export {}:{} not found or not a function", module_name, field_name)
			)
		)?.clone();
		Ok(FuncInstance::alloc_host(signature.clone(), func_idx))
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
		let key = (module_name.as_bytes().to_owned(), field_name.as_bytes().to_owned());
		let externval = self.imports.map.get(&key).ok_or_else(||
			wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
		)?;
		let memory = match *externval {
			ExternVal::Memory(ref m) => m,
			_ => return Err(
				wasmi::Error::Instantiation(format!("Export {}:{} is not a memory", module_name, field_name))
			),
		};
		Ok(memory.memref.clone())
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

pub struct InstanceImp {
	instance: ModuleRef,
	externals: ImportsExternals,
}

impl InstanceImp {
	pub fn new(code: &[u8], imports: &Imports) -> InstanceImp {
		// TODO: Return `Result`
		// TODO: Support start
		let module = Module::from_buffer(code).unwrap();

		let imports_adapter = ImportsAdapter::new(imports);

		let instance = ModuleInstance::new(
			&module,
			&imports_adapter,
		).unwrap().assert_no_start();

		let externals = imports_adapter.into_externals();

		InstanceImp {
			instance,
			externals,
		}
	}

	pub fn invoke(&mut self, name: &[u8], _args: &[Value]) -> Result<Option<Value>, Error> {
		// TODO: Convert args into `RuntimeValue` and use it.
		let name = String::from_utf8_lossy(name);
		let result = self.instance.invoke_export(&*name, &[], &mut self.externals);

		//
		match result {
			// TODO: Convert value
			Ok(_) => Ok(None),
			Err(_err) => Err(Error::Trap),
		}
	}
}
