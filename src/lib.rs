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
// Public modules
//------------------------------------------------------------------------

//------------------------------------------------------------------------
// Private modules
//------------------------------------------------------------------------
#[macro_use]
mod macros;
mod mimc_hash;
mod conversions;
mod gadget;
mod bounds_check;
#[macro_use]
mod merkle_tree;
mod commitments;
mod tests;
