#![feature(box_syntax, box_patterns)]

//------------------------------------------------------------------------
// External dependencies
//------------------------------------------------------------------------
extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate pkcs7;
extern crate rand;
extern crate hex;

//------------------------------------------------------------------------
// Modules containing macros
//------------------------------------------------------------------------
#[macro_use]
mod macros;
#[macro_use]
pub mod merkle_tree;

//------------------------------------------------------------------------
// Public modules
//------------------------------------------------------------------------
pub mod commitments;
pub mod bounds_check;
pub mod mimc_hash;
pub mod gadget;

//------------------------------------------------------------------------
// Private modules
//------------------------------------------------------------------------
mod conversions;
mod tests;
