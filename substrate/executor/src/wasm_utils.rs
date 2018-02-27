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

//! Rust implementation of Substrate contracts.

use wasmi::{ValueType, RuntimeValue, HostError};
use std::fmt;

#[derive(Debug)]
pub struct DummyUserError;
impl fmt::Display for DummyUserError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "DummyUserError")
	}
}
impl HostError for DummyUserError {
}

pub trait ConvertibleToWasm { const VALUE_TYPE: ValueType; type NativeType; fn to_runtime_value(self) -> RuntimeValue; }
impl ConvertibleToWasm for i32 { type NativeType = i32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self) } }
impl ConvertibleToWasm for u32 { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as i32) } }
impl ConvertibleToWasm for i64 { type NativeType = i64; const VALUE_TYPE: ValueType = ValueType::I64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I64(self) } }
impl ConvertibleToWasm for u64 { type NativeType = u64; const VALUE_TYPE: ValueType = ValueType::I64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I64(self as i64) } }
impl ConvertibleToWasm for f32 { type NativeType = f32; const VALUE_TYPE: ValueType = ValueType::F32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::F32(self) } }
impl ConvertibleToWasm for f64 { type NativeType = f64; const VALUE_TYPE: ValueType = ValueType::F64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::F64(self) } }
impl ConvertibleToWasm for isize { type NativeType = i32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as i32) } }
impl ConvertibleToWasm for usize { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as u32 as i32) } }
impl<T> ConvertibleToWasm for *const T { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as isize as i32) } }
impl<T> ConvertibleToWasm for *mut T { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as isize as i32) } }

#[macro_export]
macro_rules! convert_args {
	() => ([]);
	( $( $t:ty ),* ) => ( [ $( { use $crate::wasm_utils::ConvertibleToWasm; <$t>::VALUE_TYPE }, )* ] );
}

#[macro_export]
macro_rules! gen_signature {
	( ( $( $params: ty ),* ) ) => (
		{
			$crate::wasmi::Signature::new(&convert_args!($($params),*)[..], None)
		}
	);

	( ( $( $params: ty ),* ) -> $returns: ty ) => (
		{
			$crate::wasmi::Signature::new(&convert_args!($($params),*)[..], Some({ use $crate::wasm_utils::ConvertibleToWasm; <$returns>::VALUE_TYPE }))
		}
	);
}

#[macro_export]
macro_rules! check_signature {
	( @iter $index:expr, $index_ident:ident, $signature:ident,  ) => ({
		panic!("fn with index {} is undefined", $index);
	});

	( @iter $index:expr, $index_ident:ident, $signature:ident, ( ( $( $params:ty ),* ) $( -> $returns:ty )* ) $(, $tail:tt)* ) => (
		if $index_ident == $index {
			return signature_equals!($signature, ( $( $params ),* ) $( -> $returns )* );
		}
		check_signature!(@iter $index + 1, $index_ident, $signature, $($tail),* );
	);

	( $index_ident:ident, $signature:ident, $( ( $( $params:ty ),* ) $( -> $returns:ty )*),* ) => (
		check_signature!(@iter 0, $index_ident, $signature, $( ( ( $( $params ),* ) $( -> $returns )* ) ),* );
	);
}

macro_rules! resolve_fn {
	(@iter $index:expr, $sig_var:ident, $name_var:ident) => ();
	(@iter $index:expr, $sig_var:ident, $name_var:ident $name:ident ( $( $params:ty ),* ) $( -> $returns:ty )* => $($tail:tt)* ) => (
		if $name_var == stringify!($name) {
			let signature = gen_signature!( ( $( $params ),* ) $( -> $returns )* );
			if $sig_var != &signature {
				return Err($crate::wasmi::Error::Instantiation(
					format!("Export {} has different signature {:?}", $name_var, $sig_var),
				));
			}
			return Ok($crate::wasmi::FuncInstance::alloc_host(signature, $index));
		}
		resolve_fn!(@iter $index + 1, $sig_var, $name_var $($tail)*)
	);

	($sig_var:ident, $name_var:ident, $($tail:tt)* ) => (
		resolve_fn!(@iter 0, $sig_var, $name_var $($tail)*);
	);
}

#[macro_export]
macro_rules! unmarshall_args {
	( $body:tt, $objectname:ident, $args_iter:ident, $args_index:ident, $( $names:ident : $params:ty ),*) => ({
		$(
			let $names : <$params as $crate::wasm_utils::ConvertibleToWasm>::NativeType =
				$args_iter.nth({
					let idx = $args_index;
					$args_index += 1;
					idx
				});
		)*
		$body
	})
}

#[inline(always)]
pub fn constrain_closure<R, F: FnOnce() -> Result<R, ::wasmi::Trap>>(f: F) -> F {
	f
}

#[macro_export]
macro_rules! marshall {
	( $args_iter:ident, $args_index:ident, $objectname:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let body = $crate::wasm_utils::constrain_closure::<<$returns as $crate::wasm_utils::ConvertibleToWasm>::NativeType, _>(|| { unmarshall_args!($body, $objectname, $args_iter, $args_index, $( $names : $params ),*) });
		let r = body()?;
		return Ok(Some({ use $crate::wasm_utils::ConvertibleToWasm; r.to_runtime_value() }))
	});
	( $args_iter:ident, $args_index:ident, $objectname:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		let body = $crate::wasm_utils::constrain_closure::<(), _>(|| { unmarshall_args!($body, $objectname, $args_iter, $args_index, $( $names : $params ),*) });
		body()?;
		return Ok(None)
	})
}

macro_rules! dispatch_fn {
	( @iter $index:expr, $index_ident:ident, $objectname:ident, $args_iter:ident, $args_index:ident) => {
		panic!("fn with index {} is undefined", $index);
	};

	( @iter $index:expr, $index_ident:ident, $objectname:ident, $args_iter:ident, $args_index:ident, $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt $($tail:tt)*) => (
		if $index_ident == $index {
			{ marshall!($args_iter, $args_index, $objectname, ( $( $names : $params ),* ) $( -> $returns )* => $body) }
		}
		dispatch_fn!( @iter $index + 1, $index_ident, $objectname, $args_iter, $args_index $($tail)*)
	);

	( $index_ident:ident, $objectname:ident, $args_iter:ident, $args_index:ident, $($tail:tt)* ) => (
		dispatch_fn!( @iter 0, $index_ident, $objectname, $args_iter, $args_index, $($tail)*);
	);
}

#[macro_export]
macro_rules! impl_function_executor {
	( $objectname:ident : $structname:ty,
	  funcs {
		  $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt , )*
	  },
	  memories {
		  $( $mem_names:ident , )*
	  },
	  => $($pre:tt)+ ) => (
		impl $( $pre ) + $structname {
			#[allow(unused)]
			fn resolver() -> &'static $crate::wasmi::ModuleImportResolver {
				struct Resolver;
				impl $crate::wasmi::ModuleImportResolver for Resolver {
					fn resolve_func(&self, name: &str, signature: &$crate::wasmi::Signature) -> ::std::result::Result<$crate::wasmi::FuncRef, $crate::wasmi::Error> {
						resolve_fn!(signature, name, $( $name( $( $params ),* ) $( -> $returns )* => )*);

						Err($crate::wasmi::Error::Instantiation(
							format!("Export {} not found", name),
						))
					}
				}
				&Resolver
			}
		}

		impl $( $pre ) + $crate::wasmi::Externals for $structname {
			fn invoke_index(
				&mut self,
				index: usize,
				args: $crate::wasmi::RuntimeArgs,
			) -> ::std::result::Result<Option<$crate::wasmi::RuntimeValue>, $crate::wasmi::Trap> {
				let $objectname = self;
				let mut args_index = 0;
				let args = args;
				dispatch_fn!(index, $objectname, args, args_index, $( $name( $( $names : $params ),* ) $( -> $returns )* => $body ),*);
			}
		}
	);
}
