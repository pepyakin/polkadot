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

//! A `CodeExecutor` specialisation which uses natively compiled runtime when the wasm to be
//! executed is equivalent to the natively compiled code.

extern crate demo_runtime;
#[macro_use] extern crate substrate_executor;
extern crate substrate_codec as codec;
extern crate substrate_state_machine as state_machine;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate demo_primitives;
extern crate ed25519;
extern crate triehash;

#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] extern crate substrate_runtime_support as runtime_support;
#[cfg(test)] #[macro_use] extern crate hex_literal;

native_executor_instance!(pub Executor, demo_runtime::api::dispatch, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::WasmExecutor;
	use codec::{Slicable, Joiner};
	use keyring::Keyring::{self, Alice, Bob};
	use runtime_support::{Hashable, StorageValue, StorageMap};
	use state_machine::{CodeExecutor, TestExternalities};
	use primitives::twox_128;
	use demo_primitives::{Hash, Header, BlockNumber, Digest};
	use demo_runtime::transaction::{Transaction, UncheckedTransaction};
	use demo_runtime::block::Block;
	use demo_runtime::runtime::staking::{FreeBalanceOf, CodeOf, balance};
	use demo_runtime::runtime::{staking, system};
	use demo_runtime::dispatch;
	use ed25519::{Public, Pair};

	const BLOATY_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");

	// TODO: move into own crate.
	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	fn tx() -> UncheckedTransaction {
		let transaction = Transaction {
			signed: Alice.into(),
			nonce: 0,
			function: dispatch::PubCall::Staking(staking::public::Call::transfer(Bob.into(), 69)),
		};
		let signature = Keyring::from_raw_public(transaction.signed).unwrap()
			.sign(&transaction.encode());

		UncheckedTransaction { transaction, signature }
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![0u8; 8],
			twox_128(&system::BlockHashAt::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&Header::from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn panic_execution_with_native_equivalent_code_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![0u8; 8],
			twox_128(&system::BlockHashAt::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&Header::from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![0u8; 8],
			twox_128(&system::BlockHashAt::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, COMPACT_CODE, "initialise_block", &vec![].and(&Header::from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, COMPACT_CODE, "execute_transaction", &vec![].and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 42);
			assert_eq!(balance(&Bob), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![0u8; 8],
			twox_128(&system::BlockHashAt::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let r = Executor::new().call(&mut t, BLOATY_CODE, "initialise_block", &vec![].and(&Header::from_block_number(1u64)));
		assert!(r.is_ok());
		let r = Executor::new().call(&mut t, BLOATY_CODE, "execute_transaction", &vec![].and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 42);
			assert_eq!(balance(&Bob), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		staking::testing::externalities(2, 2, 0)
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transaction>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|transaction| {
			let signature = Pair::from(Keyring::from_public(Public::from_raw(transaction.signed)).unwrap())
				.sign(&transaction.encode());

			UncheckedTransaction { transaction, signature }
		}).collect::<Vec<_>>();

		let transaction_root = ordered_trie_root(transactions.iter().map(Slicable::encode)).0.into();

		let header = Header {
			parent_hash,
			number,
			state_root,
			transaction_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.blake2_256();

		(Block { header, transactions }.encode(), hash.into())
	}

	fn block1() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			hex!("7a388ce5b4eeadbb9268ae96e8822b223f4fd1841327d99f4e1c21fad81f97f2").into(),
			vec![Transaction {
				signed: Alice.into(),
				nonce: 0,
				function: dispatch::PubCall::Staking(staking::public::Call::transfer(Bob.into(), 69)),
			}]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1().1,
			hex!("e4eb71be8b816f2061f32f284e9b429562cdc1b82f11725e5f965ff23439f5e9").into(),
			vec![
				Transaction {
					signed: Bob.into(),
					nonce: 0,
					function: dispatch::PubCall::Staking(staking::public::Call::transfer(Alice.into(), 5)),
				},
				Transaction {
					signed: Alice.into(),
					nonce: 1,
					function: dispatch::PubCall::Staking(staking::public::Call::transfer(Bob.into(), 15)),
				}
			]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext();

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 41);
			assert_eq!(balance(&Bob), 69);
		});

		Executor::new().call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 30);
			assert_eq!(balance(&Bob), 78);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext();

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block1().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 41);
			assert_eq!(balance(&Bob), 69);
		});

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 30);
			assert_eq!(balance(&Bob), 78);
		});
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![0u8; 8],
			twox_128(&system::BlockHashAt::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&Header::from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].and(&tx()));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![0u8; 8],
			twox_128(&system::BlockHashAt::key_for(0)).to_vec() => vec![0u8; 32]
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&Header::from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].and(&tx()));
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 42);
			assert_eq!(balance(&Bob), 69);
		});
	}

	const TRANSFER_WASM: &[u8] = include_bytes!(
		concat!(env!("CARGO_MANIFEST_DIR"), "/../runtime/wasm-tests/bin/transfer.wasm")
	);

	#[test]
	fn wasm_test() {
		let eve = [0xAAu8; 32];

		let mut t: TestExternalities = map![
			twox_128(staking::TransactionFee::key()).to_vec() => vec![].and(&0u64),
			twox_128(&system::BlockHashAt::key_for(0)).to_vec() => vec![0u8; 32],
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![].and(&111u64),
			twox_128(&FreeBalanceOf::key_for(*Bob)).to_vec() => vec![].and(&0u64),
			twox_128(&CodeOf::key_for(*Bob)).to_vec() => TRANSFER_WASM.to_vec().encode(),
			twox_128(&FreeBalanceOf::key_for(eve)).to_vec() => vec![].and(&30u64)
		];

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "initialise_block", &vec![].and(&Header::from_block_number(1u64)));
		if r.is_err() {
			panic!("initialise_block: {:?}", r);
		}
		let r = WasmExecutor.call(&mut t, &foreign_code[..], "execute_transaction", &vec![].and(&tx()));
		if r.is_err() {
			panic!("execute_transaction: {:?}", r);
		}

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(balance(&Alice), 42);
			assert_eq!(balance(&Bob), 63);
			assert_eq!(balance(&eve), 36);
		});
	}
}
