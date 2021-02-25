#![cfg_attr(not(feature = "std"), no_std)]

//! A simple Substrate pallet that demonstrates declaring dispatchable functions, and
//! Printing text to the terminal.

use frame_support::{decl_module, decl_storage, };
use frame_system::{self as system};
use sp_std::vec::Vec;


pub trait Trait: system::Trait {}

decl_storage! {
	trait Store for Module<T: Trait> as Token {
		
		pub Parking get(fn get_parking_space): map hasher(blake2_128_concat) Vec<u8> => bool;

		pub ParkingState get(fn parking_state): bool;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {	}
}