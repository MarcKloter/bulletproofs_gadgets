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
extern crate regex;
#[macro_use]
extern crate lalrpop_util;

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
pub mod equality;
pub mod inequality;
pub mod gadget;
pub mod conversions;
pub mod utils;
pub mod lalrpop;

//------------------------------------------------------------------------
// Private modules
//------------------------------------------------------------------------
