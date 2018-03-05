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

//! Staking manager: Handles balances and periodically determines the best set of validators.

use rstd::prelude::*;
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use runtime_io::{print, blake2_256};
use codec::KeyedVec;
use runtime_support::{storage, StorageVec};
use demo_primitives::{BlockNumber, AccountId};
use runtime::{system, session, governance};
use runtime_sandbox as sandbox;

/// The balance of an account.
pub type Balance = u64;

/// The amount of bonding period left in an account. Measured in eras.
pub type Bondage = u64;

struct IntentionStorageVec {}
impl StorageVec for IntentionStorageVec {
	type Item = AccountId;
	const PREFIX: &'static[u8] = b"sta:wil:";
}

const BONDING_DURATION: &[u8] = b"sta:loc";
const VALIDATOR_COUNT: &[u8] = b"sta:vac";
const SESSIONS_PER_ERA: &[u8] = b"sta:spe";
const NEXT_SESSIONS_PER_ERA: &[u8] = b"sta:nse";
const CURRENT_ERA: &[u8] = b"sta:era";
const LAST_ERA_LENGTH_CHANGE: &[u8] = b"sta:lec";
const TOTAL_STAKE: &[u8] = b"sta:tot";

const BALANCE_OF: &[u8] = b"sta:bal:";
const BONDAGE_OF: &[u8] = b"sta:bon:";
const CODE_OF: &[u8] = b"sta:cod:";
const STORAGE_OF: &[u8] = b"sta:sto:";

/// The length of the bonding duration in eras.
pub fn bonding_duration() -> BlockNumber {
	storage::get_or_default(BONDING_DURATION)
}

/// The length of a staking era in sessions.
pub fn validator_count() -> usize {
	storage::get_or_default::<u32>(VALIDATOR_COUNT) as usize
}

/// The length of a staking era in blocks.
pub fn era_length() -> BlockNumber {
	sessions_per_era() * session::length()
}

/// The length of a staking era in sessions.
pub fn sessions_per_era() -> BlockNumber {
	storage::get_or_default(SESSIONS_PER_ERA)
}

/// The current era index.
pub fn current_era() -> BlockNumber {
	storage::get_or_default(CURRENT_ERA)
}

/// The block number at which the era length last changed.
pub fn last_era_length_change() -> BlockNumber {
	storage::get_or_default(LAST_ERA_LENGTH_CHANGE)
}

/// The balance of a given account.
pub fn balance(who: &AccountId) -> Balance {
	storage::get_or_default(&who.to_keyed_vec(BALANCE_OF))
}

/// The liquidity-state of a given account.
pub fn bondage(who: &AccountId) -> Bondage {
	storage::get_or_default(&who.to_keyed_vec(BONDAGE_OF))
}

/// The total amount of stake on the system.
pub fn total_stake() -> Balance {
	storage::get_or(TOTAL_STAKE, 0)
}

// Each identity's stake may be in one of three bondage states, given by an integer:
// - n | n <= current_era(): inactive: free to be transferred.
// - ~0: active: currently representing a validator.
// - n | n > current_era(): deactivating: recently representing a validator and not yet
//   ready for transfer.

pub mod public {
	use super::*;

	type State = BTreeMap<AccountId, (Option<Balance>, Option<Vec<u8>>, BTreeMap<Vec<u8>, Option<Vec<u8>>>)>;

	trait AccountDb {
		fn get_storage(&self, account: &AccountId, location: &[u8]) -> Option<Vec<u8>>;
		fn get_code(&self, account: &AccountId) -> Vec<u8>;
		fn get_balance(&self, account: &AccountId) -> Balance;

		fn set_storage(&self, account: &AccountId, location: Vec<u8>, value: Option<Vec<u8>>);
		fn set_code(&self, account: &AccountId, code: Vec<u8>);
		fn set_balance(&self, account: &AccountId, balance: Balance);

		fn merge(&self, state: State);
	}

	struct DirectAccountDb;
	impl AccountDb for DirectAccountDb {
		fn get_storage(&self, account: &AccountId, location: &[u8]) -> Option<Vec<u8>> {
			let mut v = account.to_keyed_vec(STORAGE_OF);
			v.extend(location);
			storage::get_raw(&v)
		}
		fn get_code(&self, account: &AccountId) -> Vec<u8> {
			storage::get_raw(&account.to_keyed_vec(CODE_OF)).unwrap_or_default()
		}
		fn get_balance(&self, account: &AccountId) -> Balance {
			storage::get_or_default::<Balance>(&account.to_keyed_vec(BALANCE_OF))
		}
		fn set_storage(&self, account: &AccountId, location: Vec<u8>, value: Option<Vec<u8>>) {
			let mut key = account.to_keyed_vec(STORAGE_OF);
			key.extend(location);
			if let Some(value) = value {
				storage::put_raw(&key, &value);
			} else {
				storage::kill(&key);
			}
		}
		fn set_code(&self, account: &AccountId, code: Vec<u8>) {
			storage::put(&account.to_keyed_vec(CODE_OF), &code);
		}
		fn set_balance(&self, account: &AccountId, balance: Balance) {
			storage::put(&account.to_keyed_vec(BALANCE_OF), &balance);
		}
		fn merge(&self, s: State) {
			for (address, (maybe_balance, maybe_code, storage)) in s.into_iter() {
				if let Some(balance) = maybe_balance {
					storage::put(&address.to_keyed_vec(BALANCE_OF), &balance);
				}
				if let Some(code) = maybe_code {
					storage::put(&address.to_keyed_vec(CODE_OF), &code);
				}
				let storage_key = address.to_keyed_vec(STORAGE_OF);
				for (k, v) in storage.into_iter() {
					let mut key = storage_key.clone();
					key.extend(k);
					if let Some(value) = v {
						storage::put_raw(&key, &value);
					} else {
						storage::kill(&key);
					}
				}
			}
		}
	}

	struct OverlayAccountDb<'a> {
		local: RefCell<State>,
		ext: &'a AccountDb,
	}
	impl<'a> OverlayAccountDb<'a> {
		fn new(ext: &'a AccountDb) -> OverlayAccountDb<'a> {
			OverlayAccountDb {
				local: RefCell::new(State::new()),
				ext,
			}
		}

		fn into_state(self) -> State {
			self.local.into_inner()
		}
	}
	impl<'a> AccountDb for OverlayAccountDb<'a> {
		fn get_storage(&self, account: &AccountId, location: &[u8]) -> Option<Vec<u8>> {
			self.local.borrow().get(account)
				.and_then(|a| a.2.get(location))
				.cloned()
				.unwrap_or_else(|| self.ext.get_storage(account, location))
		}
		fn get_code(&self, account: &AccountId) -> Vec<u8> {
			self.local.borrow().get(account)
				.and_then(|a| a.1.clone())
				.unwrap_or_else(|| self.ext.get_code(account))
		}
		fn get_balance(&self, account: &AccountId) -> Balance {
			self.local.borrow().get(account)
				.and_then(|a| a.0)
				.unwrap_or_else(|| self.ext.get_balance(account))
		}
		fn set_storage(&self, account: &AccountId, location: Vec<u8>, value: Option<Vec<u8>>) {
			self.local.borrow_mut()
				.entry(account.clone())
				.or_insert((None, None, Default::default()))
				.2.insert(location, value);
		}
		fn set_code(&self, account: &AccountId, code: Vec<u8>) {
			self.local.borrow_mut()
				.entry(account.clone())
				.or_insert((None, None, Default::default()))
				.1 = Some(code);
		}
		fn set_balance(&self, account: &AccountId, balance: Balance) {
			self.local.borrow_mut()
				.entry(account.clone())
				.or_insert((None, None, Default::default()))
				.0 = Some(balance);
		}
		fn merge(&self, s: State) {
			let mut local = self.local.borrow_mut();

			for (address, (maybe_balance, maybe_code, storage)) in s.into_iter() {
				match local.entry(address) {
					Entry::Occupied(e) => {
						let mut value = e.into_mut();
						if maybe_balance.is_some() {
							value.0 = maybe_balance;
						}
						if maybe_code.is_some() {
							value.1 = maybe_code;
						}
						value.2.extend(storage.into_iter());
					}
					Entry::Vacant(e) => {
						e.insert((maybe_balance, maybe_code, storage));
					}
				}
			}
		}
	}

	/// Create a smart-contract account.
	pub fn create(transactor: &AccountId, code: &[u8], value: Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = effect_create(transactor, code, value, DirectAccountDb) {
			DirectAccountDb.merge(commit);
		}
	}

	/// Returns an address at which smart-contract created by `transactor` with the given `code`
	/// should be placed after the creation.
	pub(super) fn derive_contract_address(transactor: &AccountId, code: &[u8]) -> [u8; 32] {
		let mut dest_pre = blake2_256(code).to_vec();
		dest_pre.extend(&transactor[..]);
		blake2_256(&dest_pre)
	}

	fn effect_create<E: AccountDb>(
		transactor: &AccountId,
		code: &[u8],
		value: Balance,
		ext: E
	) -> Option<State> {
		let from_balance = ext.get_balance(transactor);
		// TODO: a fee.
		assert!(from_balance >= value);

		let dest = derive_contract_address(transactor, code);

		// early-out if degenerate.
		if &dest == transactor {
			return None;
		}

		let mut overlay = OverlayAccountDb::new(&ext);

		// two inserts are safe
		assert!(&dest != transactor);
		overlay.set_balance(&dest, value);
		overlay.set_code(&dest, code.to_vec());
		overlay.set_balance(transactor, from_balance - value);

		Some(overlay.into_state())
	}

	/// Transfer some unlocked staking balance to another staker.
	/// TODO: probably want to state gas-limit and gas-price.
	pub fn transfer(transactor: &AccountId, dest: &AccountId, value: Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = effect_transfer(transactor, dest, value, DirectAccountDb) {
			DirectAccountDb.merge(commit);
		}
	}

	fn effect_transfer<E: AccountDb>(
		transactor: &AccountId,
		dest: &AccountId,
		value: Balance,
		ext: E
	) -> Option<State> {
		let from_balance = ext.get_balance(transactor);
		assert!(from_balance >= value);

		let to_balance = ext.get_balance(dest);
		assert!(bondage(transactor) <= bondage(dest));
		assert!(to_balance + value > to_balance);	// no overflow

		// TODO: a fee, based upon gaslimit/gasprice.
		// TODO: consider storing upper-bound for contract's gas limit in fixed-length runtime
		// code in contract itself and use that.

		// Our local overlay: Should be used for any transfers and creates that happen internally.
		let overlay = OverlayAccountDb::new(&ext);

		if transactor != dest {
			overlay.set_balance(transactor, from_balance - value);
			overlay.set_balance(dest, to_balance + value);
		}

		let dest_code = ext.get_code(dest);
		let should_commit = if dest_code.is_empty() {
			true
		} else {
			execute(&dest_code, dest, &overlay)
		};

		if should_commit {
			Some(overlay.into_state())
		} else {
			None
		}
	}

	fn execute<E: AccountDb>(code: &[u8], account: &AccountId, account_db: &E) -> bool {
		// TODO: Inspect the binary to extract the initial page count.
		let memory: RefCell<sandbox::Memory> = RefCell::new(sandbox::Memory::new(1, None));

		let ext_put_storage = |args: &[sandbox::Value]| {
			let location_ptr = args[0].as_i32() as u32;
			let value_non_null = args[1].as_i32() as u32;
			let value_ptr = args[2].as_i32() as u32;

			let mut location = [0; 32];
			memory.borrow().get(location_ptr, &mut location);

			if value_non_null != 0 {
				let mut value = [0; 32];
				memory.borrow().get(value_ptr, &mut value);

				account_db.set_storage(account, location.to_vec(), Some(value.to_vec()));
			} else {
				account_db.set_storage(account, location.to_vec(), None);
			}
		};

		let ext_get_storage = |args: &[sandbox::Value]| {
			let location_ptr = args[0].as_i32() as u32;

			let mut location = [0; 32];
			memory.borrow().get(location_ptr, &mut location);

			account_db.get_storage(account, &location);
		};

		let ext_transfer = |args: &[sandbox::Value]| {
			// ext_transfer(transfer_to: u32, value: u32)
			let transfer_to_ptr = args[0].as_i32() as u32;
			// TODO: This isn't a u32 but u64. But oh well...
			let value = args[1].as_i32() as u64;

			let mut transfer_to = [0; 32];
			memory.borrow().get(transfer_to_ptr, &mut transfer_to);

			let overlay = OverlayAccountDb::new(account_db);
			if let Some(commit_state) = effect_transfer(account, &transfer_to, value, overlay) {
				account_db.merge(commit_state);
			}
			// TODO: Trap?
		};

		let ext_create = |args: &[sandbox::Value]| {
			// ext_create(code_ptr: u32, code_len: u32, value: u32)
			let code_ptr = args[0].as_i32() as u32;
			let code_len = args[1].as_i32() as u32;
			let value = args[2].as_i32() as u32;

			let mut code = Vec::new();
			code.resize(code_len as usize, 0u8);
			memory.borrow().get(code_ptr, &mut code);

			let overlay = OverlayAccountDb::new(account_db);
			if let Some(commit_state) = effect_create(account, &code, value as u64, overlay) {
				account_db.merge(commit_state);
			}
			// TODO: Trap?
		};

		// TODO: Signatures.
		// TODO: Rename ext_put_storage -> ext_set_storage.
		let mut sandbox = sandbox::Sandbox::new();
		sandbox.register_closure("env", "ext_put_storage", &ext_put_storage);
		sandbox.register_closure("env", "ext_get_storage", &ext_get_storage);
		sandbox.register_closure("env", "ext_transfer", &ext_transfer);
		sandbox.register_closure("env", "ext_create", &ext_create);
		// TODO: ext_balance
		// TODO: ext_address
		// TODO: ext_callvalue
		// TODO: ext_panic
		sandbox.register_memory("env", "memory", memory.borrow().clone());

		let instance = sandbox.instantiate(code);

		instance.invoke(&mut sandbox, "call").is_ok()
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	pub fn stake(transactor: &AccountId) {
		let mut intentions = IntentionStorageVec::items();
		// can't be in the list twice.
		assert!(intentions.iter().find(|t| *t == transactor).is_none(), "Cannot stake if already staked.");
		intentions.push(transactor.clone());
		IntentionStorageVec::set_items(&intentions);
		storage::put(&transactor.to_keyed_vec(BONDAGE_OF), &u64::max_value());
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	pub fn unstake(transactor: &AccountId) {
		let mut intentions = IntentionStorageVec::items();
		if let Some(position) = intentions.iter().position(|t| t == transactor) {
			intentions.swap_remove(position);
		} else {
			panic!("Cannot unstake if not already staked.");
		}
		IntentionStorageVec::set_items(&intentions);
		storage::put(&transactor.to_keyed_vec(BONDAGE_OF), &(current_era() + bonding_duration()));
	}
}

pub mod privileged {
	use super::*;

	/// Set the number of sessions in an era.
	pub fn set_sessions_per_era(new: BlockNumber) {
		storage::put(NEXT_SESSIONS_PER_ERA, &new);
	}

	/// The length of the bonding duration in eras.
	pub fn set_bonding_duration(new: BlockNumber) {
		storage::put(BONDING_DURATION, &new);
	}

	/// The length of a staking era in sessions.
	pub fn set_validator_count(new: u32) {
		storage::put(VALIDATOR_COUNT, &new);
	}

	/// Force there to be a new era. This also forces a new session immediately after.
	pub fn force_new_era() {
		new_era();
		session::privileged::force_new_session();
	}
}

pub mod internal {
	use super::*;

	/// Hook to be called after to transaction processing.
	pub fn check_new_era() {
		// check block number and call new_era if necessary.
		if (system::block_number() - last_era_length_change()) % era_length() == 0 {
			new_era();
		}
	}
}

/// The era has changed - enact new staking set.
///
/// NOTE: This always happens immediately before a session change to ensure that new validators
/// get a chance to set their session keys.
fn new_era() {
	// Inform governance module that it's the end of an era
	governance::internal::end_of_an_era();

	// Increment current era.
	storage::put(CURRENT_ERA, &(current_era() + 1));

	// Enact era length change.
	let next_spe: u64 = storage::get_or_default(NEXT_SESSIONS_PER_ERA);
	if next_spe > 0 && next_spe != sessions_per_era() {
		storage::put(SESSIONS_PER_ERA, &next_spe);
		storage::put(LAST_ERA_LENGTH_CHANGE, &system::block_number());
	}

	// evaluate desired staking amounts and nominations and optimise to find the best
	// combination of validators, then use session::internal::set_validators().
	// for now, this just orders would-be stakers by their balances and chooses the top-most
	// validator_count() of them.
	let mut intentions = IntentionStorageVec::items()
		.into_iter()
		.map(|v| (balance(&v), v))
		.collect::<Vec<_>>();
	intentions.sort_unstable_by(|&(b1, _), &(b2, _)| b2.cmp(&b1));
	session::internal::set_validators(
		&intentions.into_iter()
			.map(|(_, v)| v)
			.take(validator_count())
			.collect::<Vec<_>>()
	);
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;
	use super::public::*;
	use super::privileged::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring;
	use environment::with_env;
	use demo_primitives::AccountId;
	use runtime::{staking, session};

	#[test]
	fn staking_should_work() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let four = [4u8; 32];

		let mut t: TestExternalities = map![
			twox_128(b"ses:len").to_vec() => vec![].and(&1u64),
			twox_128(b"ses:val:len").to_vec() => vec![].and(&2u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => vec![10; 32],
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => vec![20; 32],
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].and(&2u64),
			twox_128(VALIDATOR_COUNT).to_vec() => vec![].and(&2u32),
			twox_128(BONDING_DURATION).to_vec() => vec![].and(&3u64),
			twox_128(TOTAL_STAKE).to_vec() => vec![].and(&100u64),
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&10u64),
			twox_128(&two.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&20u64),
			twox_128(&three.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&30u64),
			twox_128(&four.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&40u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(validator_count(), 2usize);
			assert_eq!(bonding_duration(), 3u64);
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 1: Add three validators. No obvious change.
			with_env(|e| e.block_number = 1);
			stake(&one);
			stake(&two);
			stake(&four);
			check_new_era();
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 2: New validator set now.
			with_env(|e| e.block_number = 2);
			check_new_era();
			assert_eq!(session::validators(), vec![four.clone(), two.clone()]);

			// Block 3: Unstake highest, introduce another staker. No change yet.
			with_env(|e| e.block_number = 3);
			stake(&three);
			unstake(&four);
			check_new_era();

			// Block 4: New era - validators change.
			with_env(|e| e.block_number = 4);
			check_new_era();
			assert_eq!(session::validators(), vec![three.clone(), two.clone()]);

			// Block 5: Transfer stake from highest to lowest. No change yet.
			with_env(|e| e.block_number = 5);
			transfer(&four, &one, 40);
			check_new_era();

			// Block 6: Lowest now validator.
			with_env(|e| e.block_number = 6);
			check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), three.clone()]);

			// Block 7: Unstake three. No change yet.
			with_env(|e| e.block_number = 7);
			unstake(&three);
			check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), three.clone()]);

			// Block 8: Back to one and two.
			with_env(|e| e.block_number = 8);
			check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), two.clone()]);
		});
	}

	#[test]
	fn staking_eras_work() {
		let mut t: TestExternalities = map![
			twox_128(b"ses:len").to_vec() => vec![].and(&1u64),
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].and(&2u64)
		];
		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 0u64);

			// Block 1: No change.
			with_env(|e| e.block_number = 1);
			check_new_era();
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 0u64);

			// Block 2: Simple era change.
			with_env(|e| e.block_number = 2);
			check_new_era();
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 1u64);

			// Block 3: Schedule an era length change; no visible changes.
			with_env(|e| e.block_number = 3);
			set_sessions_per_era(3);
			check_new_era();
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 1u64);

			// Block 4: Era change kicks in.
			with_env(|e| e.block_number = 4);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 2u64);

			// Block 5: No change.
			with_env(|e| e.block_number = 5);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 2u64);

			// Block 6: No change.
			with_env(|e| e.block_number = 6);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 2u64);

			// Block 7: Era increment.
			with_env(|e| e.block_number = 7);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 3u64);
		});
	}

	#[test]
	fn staking_balance_works() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&42u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&111u64)
		];

		with_externalities(&mut t, || {
			transfer(&one, &two, 69);
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_bonded_doesnt_work() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&111u64)
		];

		with_externalities(&mut t, || {
			stake(&one);
			transfer(&one, &two, 69);
		});
	}

	const CREATE_WASM: &[u8] = include_bytes!("/Users/pepyakin/dev/parity/temp/polkadot-demo-initial-contracts/create.wasm");
	const TRANSFER_WASM: &[u8] = include_bytes!("/Users/pepyakin/dev/parity/temp/polkadot-demo-initial-contracts/transfer.wasm");

	#[test]
	fn contract_transfer() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [0xAAu8; 32];

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&111u64),
			twox_128(&two.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&0u64),
			twox_128(&two.to_keyed_vec(CODE_OF)).to_vec() => TRANSFER_WASM.to_vec(),
			twox_128(&three.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&30u64)
		];

		with_externalities(&mut t, || {
			// Contract at the address `two` sends 6 units of the balance
			// to account at address `three`.
			transfer(&one, &two, 11);

			assert_eq!(balance(&one), 100);
			assert_eq!(balance(&two), 5);
			assert_eq!(balance(&three), 36);
		});
	}

	#[test]
	fn contract_create() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let created = derive_contract_address(&two, TRANSFER_WASM);

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&111u64),
			twox_128(&two.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&0u64),
			twox_128(&two.to_keyed_vec(CODE_OF)).to_vec() => CREATE_WASM.to_vec()
		];

		with_externalities(&mut t, || {
			// When invoked, contract at address `two` must create the 'transfer' contract.
			transfer(&one, &two, 11);

			assert_eq!(balance(&one), 100);
			assert_eq!(balance(&two), 8);
			assert_eq!(balance(&created), 3);
		});
	}
}
