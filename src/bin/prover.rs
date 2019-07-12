extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
extern crate hex;
#[macro_use]
extern crate bulletproofs_gadgets;

use bulletproofs::r1cs::Prover;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;
use bulletproofs_gadgets::commitments::*;
use bulletproofs_gadgets::gadget::Gadget;
use bulletproofs_gadgets::merkle_tree::merkle_tree_gadget::{MerkleTree256, Pattern, Pattern::*};
use bulletproofs_gadgets::bounds_check::bounds_check_gadget::BoundsCheck;
use bulletproofs_gadgets::mimc_hash::mimc_hash_gadget::MimcHash256;

use std::collections::HashMap;
use std::io::prelude::*;
use std::fs::File;

/*
TODO: Accepting Command Line Arguments https://doc.rust-lang.org/book/ch12-01-accepting-command-line-arguments.html

BOUND W1 I1 I2
HASH W2 W1
MERKLE I3 W2 W3

W1 = 67
I1 = 10
I2 = 100
I3 = ROOT_HASH
W2 = HASH
W3 = HASH

match(x) {
    BOUND_regex:
        let g1 = BoundCheck:new(d["I1"] as u64, d["I2"] as u64);
        let comms = g1.
        // add comms to global commitment hashmap with current regex matching as name (so verifier can do the same)

    MERKLE_regex:
        
}
*/
    
fn main() -> std::io::Result<()> {
    // ---------- SETUP ----------
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(8192, 1);

    // ---------- CREATE PROVER ----------
    let mut prover_transcript = Transcript::new(b"CombinedGadgets");
    let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

    // ---------- WITNESSES ----------
    let val: Vec<u8> = vec![67];
    let (w1_scalar, w1_commitment, w1_var) = commit(&mut prover, &val);
    
    let image: Vec<u8> = vec![
        0x0c, 0xfb, 0x0c, 0x17, 0x61, 0x82, 0x11, 0xc6, 
        0x07, 0xfe, 0xbf, 0x70, 0x3a, 0xc3, 0xf3, 0x07, 
        0x8f, 0x7d, 0x96, 0x79, 0x8f, 0xae, 0x9d, 0x4a, 
        0x16, 0x82, 0xbc, 0x59, 0x2f, 0x7c, 0xb1, 0x26
    ];
    let (w2_scalar, w2_commitment, w2_var) = commit_single(&mut prover, &image);
    
    let merkle_leaf: Vec<u8> = vec![
        0x09, 0x24, 0x33, 0x33, 0xe3, 0x74, 0xe7, 0x6e, 
        0x49, 0x75, 0xab, 0x48, 0xae, 0x38, 0x24, 0x1b, 
        0xa6, 0x78, 0x05, 0xcd, 0x60, 0xf1, 0x52, 0x3e, 
        0x9b, 0x79, 0xa4, 0x8d, 0xaa, 0xc9, 0xa8, 0x4d
    ];
    let (w3_scalar, w3_commitment, w3_var) = commit_single(&mut prover, &merkle_leaf);

    // ---------- BOUNDS ----------
    let min: Vec<u8> = vec![10];
    let max: Vec<u8> = vec![100];

    let p_bounds = BoundsCheck::new(&min, &max);
    let bounds_dc = p_bounds.prove(&mut prover, &w1_scalar, &w1_var);

    // ---------- HASH ----------
    let p_hash = MimcHash256::new(w2_var.into());
    let hash_dc = p_hash.prove(&mut prover, &w1_scalar, &w1_var);

    // ---------- MERKLE ----------
    //     I1
    //    /  \
    //  W2    W3
    let root: Vec<u8> = vec![
        0x0c, 0x8c, 0x87, 0xb6, 0x48, 0xe8, 0xfa, 0x0d, 
        0x97, 0x26, 0xee, 0x82, 0x25, 0xbe, 0x06, 0x28, 
        0x79, 0x4f, 0x2e, 0x1d, 0x1a, 0xb9, 0x32, 0x42, 
        0x1d, 0x45, 0x85, 0x1a, 0x35, 0xd8, 0x1a, 0xc1
    ];
    let pattern: Pattern = hash!(V, V);

    let p_merkle = MerkleTree256::new(&root, pattern.clone());
    let merkle_dc = p_merkle.prove(&mut prover, &vec![w2_scalar, w3_scalar], &vec![w2_var, w3_var]);

    // ---------- CREATE PROOF ----------
    let proof = prover.prove(&bp_gens).unwrap();

    // ---------- WRITE PROOF TO FILE ----------
    let mut file = File::create("test.proof")?;
    file.write_all(&proof.to_bytes())?;

    // ---------- WRITE COMMITMENTS TO FILE ----------
    // TODO: when writing parser, move these .push() to the correspoding match cases
    let mut witness_commitments: Vec<CompressedRistretto> = Vec::new();
    witness_commitments.push(w1_commitment[0].clone());
    witness_commitments.push(w2_commitment.clone());
    witness_commitments.push(w3_commitment.clone());

    // NOTE (important): Commitments MUST be done beforehand (all W1-Wx)
    // otherwise the derived commitments need to be done in between (which makes things hard)

    let mut file = File::create("test.commitments")?;
    for (i, commitment) in witness_commitments.iter().enumerate() {
        let o = format!("C{}: 0x{}\n", i, hex::encode(commitment.as_bytes()));
        file.write_all(o.as_bytes())?;
    }

    // ---------- WRITE DERIVED COMMITMENTS TO FILE ----------
    // TODO: when writing parser, move these .insert() to the correspoding match cases
    let mut derived_commitments: HashMap<String, CompressedRistretto> = HashMap::new();
    // NOTE: this numbering is done so there can be variable derived commitments per gadget
    derived_commitments.insert("D1:0".to_string(), bounds_dc[0].clone());
    derived_commitments.insert("D1:1".to_string(), bounds_dc[1].clone());
    for (i, dc) in hash_dc.iter().enumerate() {
        derived_commitments.insert(format!("D2:{}", i), dc.clone());
    }
    // no derived commitment for merkle tree gadget

    for (i, commitment) in derived_commitments {
        let o = format!("{}: 0x{}\n", i, hex::encode(commitment.as_bytes()));
        file.write_all(o.as_bytes())?;
    }

    Ok(())
}