// Copyright 2018 Parity Technologies (UK) Ltd.
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

use std::collections::HashMap;
use error::{Error, ErrorKind, Result};
use wasmi::{Externals, FuncRef, ImportResolver, MemoryInstance, MemoryRef, Module, ModuleInstance,
            ModuleRef, RuntimeArgs, RuntimeValue, Trap};
use wasmi::memory_units::{Bytes, Pages};

struct Unmarshaller<'a> {
	data: &'a [u8],
	offset: usize,
}

impl<'a> Unmarshaller<'a> {
	fn new(data: &[u8]) -> Unmarshaller {
		Unmarshaller { data, offset: 0 }
	}

	fn read(&mut self) -> Result<u8> {
		// TODO: Error
		let v = self.data.get(self.offset).unwrap();
		self.offset += 1;
		Ok(*v)
	}

	fn slice(&mut self, len: usize) -> Result<&[u8]> {
		// TODO: Error
		let v = &self.data[self.offset..(self.offset + len)];
		self.offset += len;
		Ok(v)
	}
}

pub struct EnvironmentDefinition {
	func_map: HashMap<(Vec<u8>, Vec<u8>), usize>,
	memories_map: HashMap<(Vec<u8>, Vec<u8>), MemoryRef>,
	funcs: Vec<usize>,
}

impl EnvironmentDefinition {
	pub fn unmarshal(imports: &[u8], memories: &[MemoryRef]) -> EnvironmentDefinition {
		println!("imports={:?}", imports);
		let mut func_map = HashMap::new();
		let mut memories_map = HashMap::new();
		let mut funcs = Vec::new();

		let mut u = Unmarshaller::new(imports);
		let len = u.read().unwrap();
		for _ in 0..len {
			let module_len = u.read().unwrap();
			let module = u.slice(module_len as usize).unwrap().to_owned();

			let field_len = u.read().unwrap();
			let field = u.slice(field_len as usize).unwrap().to_owned();

			let kind = u.read().unwrap();
			match kind {
				0 => {
					let func_idx = u.read().unwrap();

					let externals_idx = funcs.len();
					funcs.push(func_idx as usize);

					println!(
						"host_func({}, {})",
						String::from_utf8_lossy(&module),
						String::from_utf8_lossy(&field)
					);
					println!("  externals_idx={}", externals_idx);
					println!("  original_idx={}", func_idx);
					func_map.insert((module, field), externals_idx);
				}
				1 => {
					let memory_id = u.read().unwrap();
					let memory_ref = memories.get(memory_id as usize).unwrap();

					println!(
						"memory({}, {})",
						String::from_utf8_lossy(&module),
						String::from_utf8_lossy(&field)
					);
					memories_map.insert((module, field), memory_ref.clone());
				}
				_ => panic!(),
			}
		}
		EnvironmentDefinition {
			func_map,
			memories_map,
			funcs,
		}
	}

	pub fn into_funcs(self) -> Vec<usize> {
		self.funcs
	}
}

impl ImportResolver for EnvironmentDefinition {
	fn resolve_func(
		&self,
		module_name: &str,
		field_name: &str,
		signature: &::wasmi::Signature,
	) -> ::std::result::Result<FuncRef, ::wasmi::Error> {
		let key = (
			module_name.as_bytes().to_owned(),
			field_name.as_bytes().to_owned(),
		);
		let idx = *self.func_map.get(&key).ok_or_else(|| {
			::wasmi::Error::Instantiation(format!(
				"Export {}:{} not found",
				module_name, field_name
			))
		})?;
		Ok(::wasmi::FuncInstance::alloc_host(signature.clone(), idx))
	}

	fn resolve_global(
		&self,
		_module_name: &str,
		_field_name: &str,
		_global_type: &::wasmi::GlobalDescriptor,
	) -> ::std::result::Result<::wasmi::GlobalRef, ::wasmi::Error> {
		// TODO:
		unimplemented!()
	}

	fn resolve_memory(
		&self,
		module_name: &str,
		field_name: &str,
		_memory_type: &::wasmi::MemoryDescriptor,
	) -> ::std::result::Result<MemoryRef, ::wasmi::Error> {
		let key = (
			module_name.as_bytes().to_vec(),
			field_name.as_bytes().to_vec(),
		);
		let mem = self.memories_map
			.get(&key)
			.ok_or_else(|| {
				::wasmi::Error::Instantiation(format!(
					"Export {}:{} not found",
					module_name, field_name
				))
			})?
			.clone();
		Ok(mem)
	}

	fn resolve_table(
		&self,
		_module_name: &str,
		_field_name: &str,
		_table_type: &::wasmi::TableDescriptor,
	) -> ::std::result::Result<::wasmi::TableRef, ::wasmi::Error> {
		// TODO:
		unimplemented!()
	}
}

pub trait SandboxCapabilities {
	fn sandbox_store(&self) -> &SandboxStore;
	fn with_allocated_data<R, F: FnOnce(&mut Self, u32) -> R>(&mut self, data: &[u8], f: F) -> R;
}

pub struct SandboxedEnvironment<'a, FE: SandboxCapabilities + Externals + 'a> {
	pub original_externals: &'a mut FE,
	pub instance_id: u32,
}

impl<'a, FE: SandboxCapabilities + Externals + 'a> SandboxedEnvironment<'a, FE> {
	pub fn new(original_externals: &mut FE, instance_id: u32) -> SandboxedEnvironment<FE> {
		SandboxedEnvironment {
			original_externals,
			instance_id,
		}
	}
}

impl<'a, FE: SandboxCapabilities + Externals + 'a> Externals for SandboxedEnvironment<'a, FE> {
	fn invoke_index(
		&mut self,
		index: usize,
		args: RuntimeArgs,
	) -> ::std::result::Result<Option<RuntimeValue>, Trap> {
		use byteorder::{LittleEndian, WriteBytesExt};

		println!("invoke_index({}, args={:?})", index, args);

		// Marshall arguments into byte vector.
		let mut invoke_args_data: Vec<u8> = Vec::new();
		for arg in args.as_ref() {
			match *arg {
				RuntimeValue::I32(v) => {
					invoke_args_data
						.write_u32::<LittleEndian>(v as u32)
						.unwrap();
				}
				// TODO:
				_ => unimplemented!(),
			}
		}

		let (func_idx, unmarshal_thunk) = {
			let instance =
				&self.original_externals.sandbox_store().instances[self.instance_id as usize];
			let unmarshal_thunk = instance.unmarshal_thunk.clone();
			let func_idx = instance.funcs[index];
			(func_idx, unmarshal_thunk)
		};

		self.original_externals.with_allocated_data(
			&invoke_args_data,
			|externals, invoke_args_ptr| {
				let result = ::wasmi::FuncInstance::invoke(
					&unmarshal_thunk,
					&[
						RuntimeValue::I32(invoke_args_ptr as i32),
						RuntimeValue::I32(args.len() as i32),
						RuntimeValue::I32(func_idx as i32),
					],
					externals,
				);
				result
			},
		)
	}
}

pub struct SandboxInstance {
	instance: ModuleRef,
	unmarshal_thunk: FuncRef,
	funcs: Vec<usize>,
}
impl SandboxInstance {
	pub fn new(
		instance: ModuleRef,
		unmarshal_thunk: FuncRef,
		funcs: Vec<usize>,
	) -> SandboxInstance {
		SandboxInstance {
			instance,
			unmarshal_thunk,
			funcs,
		}
	}
}

pub struct SandboxStore {
	pub instances: Vec<SandboxInstance>,
	pub memories: Vec<MemoryRef>,
}

impl SandboxStore {
	pub fn new() -> Self {
		SandboxStore {
			instances: Vec::new(),
			memories: Vec::new(),
		}
	}

	pub fn instantiate(
		&mut self,
		unmarshal_thunk: FuncRef,
		wasm: &[u8],
		raw_env_def: &[u8],
	) -> u32 {
		let env_def = EnvironmentDefinition::unmarshal(raw_env_def, &self.memories);

		// TODO: Remove unwraps and asserts.
		let module = Module::from_buffer(wasm).unwrap();
		let instance = ModuleInstance::new(&module, &env_def)
			.unwrap()
			.assert_no_start();

		let instance_idx = self.instances.len();
		self.instances.push(SandboxInstance::new(
			instance,
			unmarshal_thunk,
			env_def.into_funcs(),
		));

		instance_idx as u32
	}

	pub fn new_memory(&mut self, initial: u32, maximum: Option<u32>) -> u32 {
		let mem =
			MemoryInstance::alloc(Pages(initial as usize), maximum.map(|m| Pages(m as usize)))
				.unwrap();
		self.memories.push(mem);
		let mem_idx = self.memories.len() - 1;
		mem_idx as u32
	}

	pub fn instance(&self, instance_id: u32) -> Option<ModuleRef> {
		self.instances
			.get(instance_id as usize)
			.map(|i| i.instance.clone())
	}
}
