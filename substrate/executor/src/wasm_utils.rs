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

use std::sync::{Arc};
use std::collections::HashMap;
use std::result;
// pub use parity_wasm::builder;
// pub use parity_wasm::elements::{ValueType, Module};
// pub use parity_wasm::interpreter::{RuntimeValue, UserFunctionDescriptor, UserFunctionExecutor,
// 	UserDefinedElements, env_native_module, DummyUserError, ExecutionParams, UserError};
// use parity_wasm::interpreter;
use wasmi::{ValueType, RuntimeValue, GlobalInstance, TableInstance, HostError};
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

// #[macro_export]
// macro_rules! convert_args {
// 	() => ([]);
// 	( $( $t:ty ),* ) => ( [ $( { use $crate::wasm_utils::ConvertibleToWasm; <$t>::VALUE_TYPE }, )* ] );
// }

// #[macro_export]
// macro_rules! convert_fn {
// 	( $name:ident ( $( $params:ty ),* ) ) => ( $crate::wasm_utils::UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params),*), None) );
// 	( $name:ident ( $( $params:ty ),* ) -> $returns:ty ) => ( $crate::wasm_utils::UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params),*), Some({ use $crate::wasm_utils::ConvertibleToWasm; <$returns>::VALUE_TYPE }) ) );
// }

// #[macro_export]
// macro_rules! reverse_params {
// 	// Entry point, use brackets to recursively reverse above.
// 	($body:tt, $self:ident, $context:ident, $( $names:ident : $params:ty ),*) => (
// 		reverse_params!($body $self $context [ $( $names : $params ),* ]);
// 	);
// 	($body:tt $self:ident $context:ident [] $( $names:ident : $params:ty ),*) => ({
// 		$(
// 			let $names : <$params as $crate::wasm_utils::ConvertibleToWasm>::NativeType = match $context.value_stack.pop_as() {
// 				Ok(value) => value,
// 				Err(error) => return Err(error.into()),
// 			};
// 		)*
// 		$body
// 	});
// 	($body:tt $self:ident $context:ident [ $name:ident : $param:ty $(, $names:ident : $params:ty )* ] $( $reversed_names:ident : $reversed_params:ty ),*) => (
// 		reverse_params!($body $self $context [ $( $names : $params ),* ] $name : $param $( , $reversed_names : $reversed_params )*);
// 	);
// }

// #[macro_export]
// macro_rules! marshall {
// 	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
// 		reverse_params!($body, $self, $context, $( $names : $params ),*);
// 		Ok(None)
// 	});
// 	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
// 		let r : <$returns as $crate::wasm_utils::ConvertibleToWasm>::NativeType = reverse_params!($body, $self, $context, $( $names : $params ),*);
// 		Ok(Some({ use $crate::wasm_utils::ConvertibleToWasm; r.to_runtime_value() }))
// 	})
// }

// #[macro_export]
// macro_rules! dispatch {
// 	( $objectname:ident, $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt ),* ) => (
// 		fn execute(&mut self, name: &str, context: $crate::wasm_utils::CallerContext)
// 			-> $crate::wasm_utils::result::Result<Option<$crate::wasm_utils::RuntimeValue>, $crate::wasm_utils::Error> {
// 			let $objectname = self;
// 			match name {
// 				$(
// 					stringify!($name) => marshall!(context, $objectname, ( $( $names : $params ),* ) $( -> $returns )* => $body),
// 				)*
// 				_ => panic!()
// 			}
// 		}
// 	);
// }

// #[macro_export]
// macro_rules! signatures {
// 	( $( $name:ident ( $( $params:ty ),* ) $( -> $returns:ty )* ),* ) => (
// 		const SIGNATURES: &'static [$crate::wasm_utils::UserFunctionDescriptor] = &[
// 			$(
// 				convert_fn!( $name ( $( $params ),* ) $( -> $returns )* ),
// 			)*
// 		];
// 	);
// }

// pub trait IntoUserDefinedElements {
// 	fn into_user_defined_elements(&mut self) -> UserDefinedElements<DummyUserError>;
// }

// #[macro_export]
// macro_rules! impl_function_executor {
// 	( $objectname:ident : $structname:ty, $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt ),* => $($pre:tt)+ ) => (
// 		impl $($pre)+ $crate::wasm_utils::UserFunctionExecutor<$crate::wasm_utils::DummyUserError> for $structname {
// 			dispatch!($objectname, $( $name( $( $names : $params ),* ) $( -> $returns )* => $body ),*);
// 		}
// 		impl $($pre)+ $structname {
// 			signatures!($( $name( $( $params ),* ) $( -> $returns )* ),*);
// 		}
// 		impl $($pre)+ $crate::wasm_utils::IntoUserDefinedElements for $structname {
// 			fn into_user_defined_elements(&mut self) -> UserDefinedElements<$crate::wasm_utils::DummyUserError> {
// 				$crate::wasm_utils::UserDefinedElements {
// 					executor: Some(self),
// 					globals: HashMap::new(),	// TODO: provide
// 					functions: ::std::borrow::Cow::from(Self::SIGNATURES),
// 				}
// 			}
// 		}
// 	);
// }

macro_rules! resolve_fn {
    (@iter $index:expr, $name_var:ident,) => ();
    (@iter $index:expr, $name_var:ident, $name:ident $($names:ident)*) => (
        if $name_var == stringify!($name) {
			// TODO: signature
			return Ok($crate::wasmi::FuncInstance::alloc_host($crate::wasmi::Signature::new(&[][..], None), $index));
        }
        resolve_fn!(@iter $index + 1, $name_var, $($names)*)
    );
    ($name_var:ident, $($names:ident),*) => (
        resolve_fn!(@iter 0, $name_var, $($names)*);
    );
}

#[macro_export]
macro_rules! convert_args {
    () => ([]);
    ( $( $t:ty ),* ) => ( [ $( { use $crate::wasm_utils::ConvertibleToWasm; <$t>::VALUE_TYPE }, )* ] );
}

#[macro_export]
macro_rules! signature_equals {
    ( $signature:ident, ( $( $params: ty ),* ) ) => (
        {
            $signature.params() == &convert_args!($($params),*) && $signature.return_type() == None
        }
    );

    ( $signature:ident, ( $( $params: ty ),* ) -> $returns: ty ) => (
        {
            $signature.params() == &convert_args!($($params),*) && $signature.return_type() == Some({ use $crate::wasm_utils::ConvertibleToWasm; <$returns>::VALUE_TYPE })
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

pub fn constrain_closure<R, F: FnOnce() -> Result<R, ::wasmi::Trap>>(f: F) -> F {
    f
}

#[macro_export]
macro_rules! marshall {
    ( $args_iter:ident, $args_index:ident, $objectname:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
        let mut body = $crate::wasm_utils::constrain_closure::<<$returns as $crate::wasm_utils::ConvertibleToWasm>::NativeType, _>(|| { unmarshall_args!($body, $objectname, $args_iter, $args_index, $( $names : $params ),*) });
        let r = body()?;
        return Ok(Some({ use $crate::wasm_utils::ConvertibleToWasm; r.to_runtime_value() }))
    });
    ( $args_iter:ident, $args_index:ident, $objectname:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
        let mut body = $crate::wasm_utils::constrain_closure::<(), _>(|| { unmarshall_args!($body, $objectname, $args_iter, $args_index, $( $names : $params ),*) });
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
            fn resolver() -> &'static $crate::wasmi::ModuleImportResolver {
                struct Resolver;
                impl $crate::wasmi::ModuleImportResolver for Resolver {
                    fn resolve_func(&self, name: &str, _signature: &$crate::wasmi::Signature) -> ::std::result::Result<$crate::wasmi::FuncRef, $crate::wasmi::Error> {
                        resolve_fn!(name, $( $name ),*);

						// TODO: Don't panic, return `Err`.
                        panic!("func with name {} not found", name);
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
                let mut $objectname = self;
				let mut args_index = 0;
                let mut args = args;
                dispatch_fn!(index, $objectname, args, args_index, $( $name( $( $names : $params ),* ) $( -> $returns )* => $body ),*);
            }
        }
    );
}

// #[derive(Clone)]
// struct DummyUserFunctionExecutor;
// impl<E: UserError> interpreter::UserFunctionExecutor<E> for DummyUserFunctionExecutor {
// 	fn execute(&mut self, _name: &str, _context: interpreter::CallerContext<E>) ->
// 		result::Result<Option<interpreter::RuntimeValue>, interpreter::Error<E>>
// 	{
// 		unimplemented!()
// 	}
// }

// pub trait AddModuleWithoutFullDependentInstance {
// 	fn add_module_by_sigs(
// 		&self,
// 		name: &str,
// 		module: Module,
// 		functions: HashMap<&str, &'static [UserFunctionDescriptor]>,
// 	) -> result::Result<Arc<interpreter::ModuleInstance<DummyUserError>>, interpreter::Error<DummyUserError>>;

// 	fn params_with_external<'a, 'b: 'a>(&'b self, externals_name: &str, externals: &'a mut IntoUserDefinedElements) -> result::Result<ExecutionParams<'a, DummyUserError>, Error>;
// }

// impl AddModuleWithoutFullDependentInstance for interpreter::ProgramInstance<DummyUserError> {
// 	fn add_module_by_sigs(
// 		&self,
// 		name: &str,
// 		module: Module,
// 		functions: HashMap<&str, &'static [UserFunctionDescriptor]>
// 	) -> result::Result<Arc<interpreter::ModuleInstance<DummyUserError>>, interpreter::Error<DummyUserError>> {
// 		let mut dufe = vec![DummyUserFunctionExecutor; functions.len()];
// 		let dufe_refs = dufe.iter_mut().collect::<Vec<_>>();
// 		let fake_module_map = functions.into_iter()
// 			.zip(dufe_refs.into_iter())
// 			.map(|((dep_mod_name, functions), dufe)| -> result::Result<_, interpreter::Error<DummyUserError>> {
// 				let fake_module = Arc::new(
// 					interpreter::env_native_module(
// 						self.module(dep_mod_name).ok_or(DummyUserError)?, UserDefinedElements {
// 							executor: Some(dufe),
// 							globals: HashMap::new(),
// 							functions: ::std::borrow::Cow::from(functions),
// 						}
// 					)?
// 				);
// 				let fake_module: Arc<interpreter::ModuleInstanceInterface<_>> = fake_module;
// 				Ok((dep_mod_name.into(), fake_module))
// 			})
// 			.collect::<result::Result<HashMap<_, _>, interpreter::Error<DummyUserError>>>()?;
// 		self.add_module(name, module, Some(&fake_module_map))
// 	}

// 	fn params_with_external<'a, 'b: 'a>(&'b self, externals_name: &str, externals: &'a mut IntoUserDefinedElements) -> result::Result<ExecutionParams<'a, DummyUserError>, Error> {
// 		Ok(interpreter::ExecutionParams::with_external(
// 			externals_name.into(),
// 			Arc::new(
// 				interpreter::env_native_module(
// 					self.module(externals_name).ok_or(DummyUserError)?,
// 					externals.into_user_defined_elements()
// 				)?
// 			)
// 		))
// 	}
// }
