extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
#[macro_use]
extern crate bulletproofs_gadgets;
extern crate regex;

use bulletproofs::r1cs::{Verifier, Variable, R1CSProof};
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
use std::io::{BufReader};
use std::fs::File;
use regex::Regex;

fn main() -> std::io::Result<()> {
    // ---------- PUBLIC VALUES ----------
    let min: Vec<u8> = vec![10];
    let max: Vec<u8> = vec![100];
    
    let root: Vec<u8> = vec![
        0x0c, 0x8c, 0x87, 0xb6, 0x48, 0xe8, 0xfa, 0x0d, 
        0x97, 0x26, 0xee, 0x82, 0x25, 0xbe, 0x06, 0x28, 
        0x79, 0x4f, 0x2e, 0x1d, 0x1a, 0xb9, 0x32, 0x42, 
        0x1d, 0x45, 0x85, 0x1a, 0x35, 0xd8, 0x1a, 0xc1
    ];
    let pattern: Pattern = hash!(V, V);

    // ---------- READ PROOF ----------
    let mut file = File::open("test.proof")?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    
    let proof = R1CSProof::from_bytes(&buffer[..]).unwrap();

    // ---------- READ COMMITMENTS ----------
    let mut commitments: HashMap<String, CompressedRistretto> = HashMap::new();

    let file = File::open("test.commitments")?;
    for line in BufReader::new(file).lines() {
        let string = line.unwrap();
        let re = Regex::new(r"^([C|D]{1}[\d|-]+?): 0x([[:alnum:]]+?)$").unwrap();
        assert!(re.is_match(&string), format!("invalid commitment entry: {}", string));
        
        let cap = re.captures(&string).unwrap();
        let bytes = hex::decode(&cap[2]).unwrap();
        let com = CompressedRistretto::from_slice(&bytes);
        commitments.insert(cap[1].to_string(), com);
    }

    // ---------- ROUTE COMMITMENTS TO GADGETS ----------
    let mut witness_commitments = Vec::new();
    witness_commitments.push(*commitments.get("C0").unwrap());
    witness_commitments.push(*commitments.get("C1").unwrap());
    witness_commitments.push(*commitments.get("C2").unwrap());

    let mut bounds_dc = Vec::new();
    bounds_dc.push(*commitments.get("D1-0").unwrap());
    bounds_dc.push(*commitments.get("D1-1").unwrap());
    let mut hash_dc = Vec::new();
    hash_dc.push(*commitments.get("D2-0").unwrap());
    hash_dc.push(*commitments.get("D2-1").unwrap());
    let merkle_dc = Vec::new();

    // ---------- VERIFIER ----------
    let v_pc_gens = PedersenGens::default();
    let v_bp_gens = BulletproofGens::new(8192, 1);
    let mut verifier_transcript = Transcript::new(b"CombinedGadgets");
    let mut verifier = Verifier::new(&mut verifier_transcript);
    let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);

    // ---------- BOUNDS ----------
    let v_bounds = BoundsCheck::new(&min, &max);
    v_bounds.verify(&mut verifier, &vec![witness_vars[0]], &bounds_dc);

    // ---------- HASH ----------
    let v_hash = MimcHash256::new(witness_vars[1].into());
    v_hash.verify(&mut verifier, &vec![witness_vars[0]], &hash_dc);

    // ---------- MERKLE ----------
    let v_merkle = MerkleTree256::new(&root, pattern.clone());
    v_merkle.verify(&mut verifier, &vec![witness_vars[1], witness_vars[2]], &merkle_dc);

    // ---------- VERIFY PROOF ----------
    assert!(verifier.verify(&proof, &v_pc_gens, &v_bp_gens).is_ok());

    Ok(())
}