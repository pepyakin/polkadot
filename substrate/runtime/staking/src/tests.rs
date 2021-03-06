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

//! Tests for the module.

use super::*;
use runtime_io::with_externalities;
use mock::*;

#[test]
fn indexing_lookup_should_work() {
	with_externalities(&mut new_test_ext(10, 1, 2, 0, true), || {
		assert_eq!(Staking::lookup_index(0), Some(1));
		assert_eq!(Staking::lookup_index(1), Some(2));
		assert_eq!(Staking::lookup_index(2), Some(3));
		assert_eq!(Staking::lookup_index(3), Some(4));
		assert_eq!(Staking::lookup_index(4), None);
	});
}

#[test]
fn default_indexing_on_new_accounts_should_work() {
	with_externalities(&mut new_test_ext(10, 1, 2, 0, true), || {
		assert_eq!(Staking::lookup_index(4), None);
		assert_ok!(Staking::transfer(&1, 5.into(), 10));
		assert_eq!(Staking::lookup_index(4), Some(5));
	});
}

#[test]
fn dust_account_removal_should_work() {
	with_externalities(&mut new_test_ext(256 * 10, 1, 2, 0, true), || {
		System::inc_account_nonce(&2);
		assert_eq!(System::account_nonce(&2), 1);
		assert_eq!(Staking::voting_balance(&2), 256 * 20);

		assert_ok!(Staking::transfer(&2, 5.into(), 256 * 10 + 1));	// index 1 (account 2) becomes zombie
		assert_eq!(Staking::voting_balance(&2), 0);
		assert_eq!(Staking::voting_balance(&5), 256 * 10 + 1);
		assert_eq!(System::account_nonce(&2), 0);
	});
}

#[test]
fn reclaim_indexing_on_new_accounts_should_work() {
	with_externalities(&mut new_test_ext(256 * 1, 1, 2, 0, true), || {
		assert_eq!(Staking::lookup_index(1), Some(2));
		assert_eq!(Staking::lookup_index(4), None);
		assert_eq!(Staking::voting_balance(&2), 256 * 20);

		assert_ok!(Staking::transfer(&2, 5.into(), 256 * 20));	// account 2 becomes zombie freeing index 1 for reclaim)
		assert_eq!(Staking::voting_balance(&2), 0);

		assert_ok!(Staking::transfer(&5, 6.into(), 256 * 1 + 0x69));	// account 6 takes index 1.
		assert_eq!(Staking::voting_balance(&6), 256 * 1 + 0x69);
		assert_eq!(Staking::lookup_index(1), Some(6));
	});
}

#[test]
fn reserved_balance_should_prevent_reclaim_count() {
	with_externalities(&mut new_test_ext(256 * 1, 1, 2, 0, true), || {
		System::inc_account_nonce(&2);
		assert_eq!(Staking::lookup_index(1), Some(2));
		assert_eq!(Staking::lookup_index(4), None);
		assert_eq!(Staking::voting_balance(&2), 256 * 20);

		assert_ok!(Staking::reserve(&2, 256 * 19 + 1));					// account 2 becomes mostly reserved
		assert_eq!(Staking::free_balance(&2), 0);						// "free" account deleted."
		assert_eq!(Staking::voting_balance(&2), 256 * 19 + 1);			// reserve still exists.
		assert_eq!(System::account_nonce(&2), 1);

		assert_ok!(Staking::transfer(&4, 5.into(), 256 * 1 + 0x69));	// account 4 tries to take index 1 for account 5.
		assert_eq!(Staking::voting_balance(&5), 256 * 1 + 0x69);
		assert_eq!(Staking::lookup_index(1), Some(2));					// but fails.
		assert_eq!(System::account_nonce(&2), 1);

		assert_eq!(Staking::slash(&2, 256 * 18 + 2), None);				// account 2 gets slashed
		assert_eq!(Staking::voting_balance(&2), 0);						// "free" account deleted."
		assert_eq!(System::account_nonce(&2), 0);

		assert_ok!(Staking::transfer(&4, 6.into(), 256 * 1 + 0x69));	// account 4 tries to take index 1 again for account 6.
		assert_eq!(Staking::voting_balance(&6), 256 * 1 + 0x69);
		assert_eq!(Staking::lookup_index(1), Some(6));					// and succeeds.
	});
}

#[test]
fn staking_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 2, 0, true), || {
		assert_eq!(Staking::era_length(), 2);
		assert_eq!(Staking::validator_count(), 2);
		assert_eq!(Staking::bonding_duration(), 3);
		assert_eq!(Session::validators(), vec![10, 20]);

		// Block 1: Add three validators. No obvious change.
		System::set_block_number(1);
		assert_ok!(Staking::stake(&1));
		assert_ok!(Staking::stake(&2));
		assert_ok!(Staking::stake(&4));
		Staking::check_new_era();
		assert_eq!(Session::validators(), vec![10, 20]);

		// Block 2: New validator set now.
		System::set_block_number(2);
		Staking::check_new_era();
		assert_eq!(Session::validators(), vec![4, 2]);

		// Block 3: Unstake highest, introduce another staker. No change yet.
		System::set_block_number(3);
		assert_ok!(Staking::stake(&3));
		assert_ok!(Staking::unstake(&4));
		Staking::check_new_era();

		// Block 4: New era - validators change.
		System::set_block_number(4);
		Staking::check_new_era();
		assert_eq!(Session::validators(), vec![3, 2]);

		// Block 5: Transfer stake from highest to lowest. No change yet.
		System::set_block_number(5);
		assert_ok!(Staking::transfer(&4, 1.into(), 40));
		Staking::check_new_era();

		// Block 6: Lowest now validator.
		System::set_block_number(6);
		Staking::check_new_era();
		assert_eq!(Session::validators(), vec![1, 3]);

		// Block 7: Unstake three. No change yet.
		System::set_block_number(7);
		assert_ok!(Staking::unstake(&3));
		Staking::check_new_era();
		assert_eq!(Session::validators(), vec![1, 3]);

		// Block 8: Back to one and two.
		System::set_block_number(8);
		Staking::check_new_era();
		assert_eq!(Session::validators(), vec![1, 2]);
	});
}

#[test]
fn staking_eras_work() {
	with_externalities(&mut new_test_ext(0, 1, 2, 0, true), || {
		assert_eq!(Staking::era_length(), 2);
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);

		// Block 1: No change.
		System::set_block_number(1);
		Staking::check_new_era();
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);

		// Block 2: Simple era change.
		System::set_block_number(2);
		Staking::check_new_era();
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 1);

		// Block 3: Schedule an era length change; no visible changes.
		System::set_block_number(3);
		assert_ok!(Staking::set_sessions_per_era(3));
		Staking::check_new_era();
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 1);

		// Block 4: Era change kicks in.
		System::set_block_number(4);
		Staking::check_new_era();
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 2);

		// Block 5: No change.
		System::set_block_number(5);
		Staking::check_new_era();
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 2);

		// Block 6: No change.
		System::set_block_number(6);
		Staking::check_new_era();
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 2);

		// Block 7: Era increment.
		System::set_block_number(7);
		Staking::check_new_era();
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 3);
	});
}

#[test]
fn staking_balance_works() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 42);
		assert_eq!(Staking::free_balance(&1), 42);
		assert_eq!(Staking::reserved_balance(&1), 0);
		assert_eq!(Staking::voting_balance(&1), 42);
		assert_eq!(Staking::free_balance(&2), 0);
		assert_eq!(Staking::reserved_balance(&2), 0);
		assert_eq!(Staking::voting_balance(&2), 0);
	});
}

#[test]
fn staking_balance_transfer_works() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::transfer(&1, 2.into(), 69));
		assert_eq!(Staking::voting_balance(&1), 42);
		assert_eq!(Staking::voting_balance(&2), 69);
	});
}

#[test]
fn staking_balance_transfer_when_bonded_should_not_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::stake(&1));
		assert_noop!(Staking::transfer(&1, 2.into(), 69), "bondage too high to send value");
	});
}

#[test]
fn reserving_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);

		assert_eq!(Staking::voting_balance(&1), 111);
		assert_eq!(Staking::free_balance(&1), 111);
		assert_eq!(Staking::reserved_balance(&1), 0);

		assert_ok!(Staking::reserve(&1, 69));

		assert_eq!(Staking::voting_balance(&1), 111);
		assert_eq!(Staking::free_balance(&1), 42);
		assert_eq!(Staking::reserved_balance(&1), 69);
	});
}

#[test]
fn staking_balance_transfer_when_reserved_should_not_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::reserve(&1, 69));
		assert_noop!(Staking::transfer(&1, 2.into(), 69), "balance too low to send value");
	});
}

#[test]
fn deducting_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::reserve(&1, 69));
		assert_eq!(Staking::free_balance(&1), 42);
	});
}

#[test]
fn deducting_balance_when_bonded_should_not_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		<Bondage<Test>>::insert(1, 2);
		System::set_block_number(1);
		assert_eq!(Staking::unlock_block(&1), LockStatus::LockedUntil(2));
		assert_noop!(Staking::reserve(&1, 69), "free funds are still bonded");
	});
}

#[test]
fn refunding_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 42);
		<ReservedBalance<Test>>::insert(1, 69);
		Staking::unreserve(&1, 69);
		assert_eq!(Staking::free_balance(&1), 111);
		assert_eq!(Staking::reserved_balance(&1), 0);
	});
}

#[test]
fn slashing_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::reserve(&1, 69));
		assert!(Staking::slash(&1, 69).is_none());
		assert_eq!(Staking::free_balance(&1), 0);
		assert_eq!(Staking::reserved_balance(&1), 42);
	});
}

#[test]
fn slashing_incomplete_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 42);
		assert_ok!(Staking::reserve(&1, 21));
		assert!(Staking::slash(&1, 69).is_some());
		assert_eq!(Staking::free_balance(&1), 0);
		assert_eq!(Staking::reserved_balance(&1), 0);
	});
}

#[test]
fn unreserving_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::reserve(&1, 111));
		Staking::unreserve(&1, 42);
		assert_eq!(Staking::reserved_balance(&1), 69);
		assert_eq!(Staking::free_balance(&1), 42);
	});
}

#[test]
fn slashing_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::reserve(&1, 111));
		assert!(Staking::slash_reserved(&1, 42).is_none());
		assert_eq!(Staking::reserved_balance(&1), 69);
		assert_eq!(Staking::free_balance(&1), 0);
	});
}

#[test]
fn slashing_incomplete_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::reserve(&1, 42));
		assert!(Staking::slash_reserved(&1, 69).is_some());
		assert_eq!(Staking::free_balance(&1), 69);
		assert_eq!(Staking::reserved_balance(&1), 0);
	});
}

#[test]
fn transferring_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 110);
		<FreeBalance<Test>>::insert(2, 1);
		assert_ok!(Staking::reserve(&1, 110));
		assert_ok!(Staking::transfer_reserved(&1, &2, 41), None);
		assert_eq!(Staking::reserved_balance(&1), 69);
		assert_eq!(Staking::free_balance(&1), 0);
		assert_eq!(Staking::reserved_balance(&2), 0);
		assert_eq!(Staking::free_balance(&2), 42);
	});
}

#[test]
fn transferring_reserved_balance_to_nonexistent_should_fail() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 111);
		assert_ok!(Staking::reserve(&1, 111));
		assert_noop!(Staking::transfer_reserved(&1, &2, 42), "beneficiary account must pre-exist");
	});
}

#[test]
fn transferring_incomplete_reserved_balance_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false), || {
		<FreeBalance<Test>>::insert(1, 110);
		<FreeBalance<Test>>::insert(2, 1);
		assert_ok!(Staking::reserve(&1, 41));
		assert!(Staking::transfer_reserved(&1, &2, 69).unwrap().is_some());
		assert_eq!(Staking::reserved_balance(&1), 0);
		assert_eq!(Staking::free_balance(&1), 69);
		assert_eq!(Staking::reserved_balance(&2), 0);
		assert_eq!(Staking::free_balance(&2), 42);
	});
}
