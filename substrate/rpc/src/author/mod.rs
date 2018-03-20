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

//! Substrate block-author/full-node API.

use primitives::block;
use client;
use state_machine;

mod error;

#[cfg(test)]
mod tests;

use self::error::{Result};

build_rpc_trait! {
	/// Polkadot blockchain API
	pub trait AuthorApi {
		/// Get header of a relay chain block.
		#[rpc(name = "author_transact")]
		fn transact(&self, block::Transaction) -> Result<()>;
	}
}

impl<B, E> AuthorApi for client::Client<B, E> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
	client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	fn transact(&self, tx: block::Transaction) -> Result<()> {
		Ok(self.submit_transaction(tx)?)
	}
}
