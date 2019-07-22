extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
#[macro_use]
extern crate bulletproofs_gadgets;
extern crate regex;

use bulletproofs::r1cs::{Prover, Variable, LinearCombination};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use bulletproofs_gadgets::commitments::*;
use bulletproofs_gadgets::gadget::Gadget;
use bulletproofs_gadgets::merkle_tree::merkle_tree_gadget::{MerkleTree256, Pattern, Pattern::*};
use bulletproofs_gadgets::bounds_check::bounds_check_gadget::BoundsCheck;
use bulletproofs_gadgets::mimc_hash::mimc_hash_gadget::MimcHash256;
use bulletproofs_gadgets::conversions::be_to_scalar;

use std::collections::HashMap;
use std::io::prelude::*;
use std::io::{BufReader};
use std::fs::File;
use std::env;
use regex::Regex;

type Commitment = (Vec<Scalar>, Vec<CompressedRistretto>, Vec<Variable>);

struct Parser {

}

impl Parser {

}

fn parse(pattern: &[String]) -> Pattern {
    match pattern[0].as_ref() {
        "(" => {
            let mut separator = 0;
            if pattern[1] != "(" {
                separator = 2;
            } else {
                let mut level = 0;
                for (i, symbol) in pattern[1..].iter().enumerate() {
                    match symbol.as_ref() {
                        "(" => level += 1,
                        ")" => {
                            level -= 1;
                            if level == 0 {
                                separator = i + 2;
                                break;
                            }
                        },
                        _ => ()
                    }
                }
            }

            return hash!(
                parse(&pattern[1..separator]), 
                parse(&pattern[separator..pattern.len()])
            );
        },
        "W" => return W,
        "I" => return I,
        _ => panic!("invalid state")
    }
}

fn main() -> std::io::Result<()> {
    // ---------- COLLECT CMD LINE ARGUMENT VALUES ----------
    let filename = Box::leak(env::args().nth(1).expect("missing argument").into_boxed_str());

    // ---------- SETUP ----------
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(8192, 1);
    // TODO: assign number of gens per gadget (shared between prover/verifier)

    // ---------- CREATE PROVER ----------
    let mut transcript = Transcript::new(filename.as_bytes());
    let mut prover = Prover::new(&pc_gens, &mut transcript);

    // ---------- ASSIGNMENTS ----------
    let mut instance_vars: HashMap<String, Vec<u8>> = HashMap::new();
    let mut witness_coms: HashMap<String, Commitment> = HashMap::new();

    let file = File::open(format!("{}.assignments", filename))?;
    for line in BufReader::new(file).lines() {
        let string = line.unwrap();
        let re = Regex::new(r"^(I\d+?) = 0x([[:alnum:]]+?)$").unwrap();
        assert!(re.is_match(&string), format!("invalid assignment entry: {}", string));

        let cap = re.captures(&string).unwrap();
        let bytes = hex::decode(&cap[2]).unwrap();
        instance_vars.insert(cap[1].to_string(), bytes);
    }

    let file = File::open(format!("{}.witnesses", filename))?;
    for line in BufReader::new(file).lines() {
        let string = line.unwrap();
        let re = Regex::new(r"^(W\d+?) = 0x([[:alnum:]]+?)$").unwrap();
        assert!(re.is_match(&string), format!("invalid assignment entry: {}", string));

        let cap = re.captures(&string).unwrap();
        let bytes = hex::decode(&cap[2]).unwrap();
        witness_coms.insert(cap[1].to_string(), commit(&mut prover, &bytes));
    }

    // ---------- GADGETS ----------
    let mut derived_coms: HashMap<String, CompressedRistretto> = HashMap::new();
    let file = File::open(format!("{}.gadgets", filename))?;
    for (index, line) in BufReader::new(file).lines().enumerate() {
        let string = line.unwrap();
        let re = Regex::new(r"^([[:alnum:]]+?) (.*)$").unwrap();
        assert!(re.is_match(&string), format!("invalid gadget entry: {}", string));
        
        let cap = re.captures(&string).unwrap();
        let gadget = cap[1].to_string();
        let args = &cap[2];

        match gadget.as_ref() {
            "BOUND" => {
                let re = Regex::new(r"^(W\d+?) (I\d+?) (I\d+?)$").unwrap();
                assert!(re.is_match(&args), format!("invalid BOUND arguments: {}", args));
                let cap = re.captures(&args).unwrap();
                
                let witness = witness_coms.get(&cap[1]).expect(&format!("missing witness var {}", &cap[1]));
                assert!(witness.0.len() == 1, format!("witness var {} is longer than 32 bytes", &cap[1]));

                let min: Vec<u8> = instance_vars.get(&cap[2]).expect(&format!("missing instance var {}", &cap[2])).to_vec();
                assert!(min.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[2]));
                let max: Vec<u8> = instance_vars.get(&cap[3]).expect(&format!("missing instance var {}", &cap[3])).to_vec();
                assert!(max.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[3]));

                let gadget = BoundsCheck::new(&min, &max);
                let coms = gadget.prove(&mut prover, &witness.0, &witness.2);

                for (i, dc) in coms.iter().enumerate() {
                    derived_coms.insert(format!("D{}-{}", index, i), dc.clone());
                }
            },
            "HASH"  => {
                let re = Regex::new(r"^(([W|I]{1})\d+?) (W\d+?)$").unwrap();
                assert!(re.is_match(&args), format!("invalid HASH arguments: {}", args));
                let cap = re.captures(&args).unwrap();

                let image: LinearCombination = match cap[2].to_string().as_ref() {
                    "W" => {
                        let com = witness_coms.get(&cap[1]).expect(&format!("missing witness var {}", &cap[1]));
                        assert!(com.0.len() == 1, format!("witness var {} is longer than 32 bytes", &cap[1]));
                        com.2[0].into()
                    },
                    "I" => {
                        let var = instance_vars.get(&cap[1]).expect(&format!("missing instance var {}", &cap[1]));
                        assert!(var.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[1]));
                        be_to_scalar(var).into()
                    },
                    _ => panic!("invalid state")
                };

                let preimage = witness_coms.get(&cap[3]).expect(&format!("missing witness var {}", &cap[3]));

                let gadget = MimcHash256::new(image);
                let coms = gadget.prove(&mut prover, &preimage.0, &preimage.2);

                for (i, dc) in coms.iter().enumerate() {
                    derived_coms.insert(format!("D{}-{}", index, i), dc.clone());
                }
            },
            "MERKLE" => {
                let re = Regex::new(r"^([W|I]{1}\d+?) (.*)$").unwrap();
                assert!(re.is_match(&args), format!("invalid MERKLE arguments: {}", args));
                let cap = re.captures(&args).unwrap();

                let root: LinearCombination = match cap[1].chars().nth(0).unwrap() {
                    'W' => {
                        let com = witness_coms.get(&cap[1]).expect(&format!("missing witness var {}", &cap[1]));
                        assert!(com.0.len() == 1, format!("witness var {} is longer than 32 bytes", &cap[1]));
                        com.2[0].into()
                    },
                    'I' => {
                        let var = instance_vars.get(&cap[1]).expect(&format!("missing instance var {}", &cap[1]));
                        assert!(var.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[1]));
                        be_to_scalar(var).into()
                    },
                    _ => panic!("invalid state")
                };

                let mut w_scalars: Vec<Scalar> = Vec::new();
                let mut w_variables: Vec<Variable> = Vec::new();
                let mut i_variables: Vec<Vec<u8>> = Vec::new();

                // parse pattern
                let re = Regex::new(r"\(|\)|W|I").unwrap();
                let mut brackets = Vec::new();
                for cap in re.captures_iter(&cap[2]) {
                    brackets.push(cap[0].to_string());
                }
                let pattern = parse(&brackets[..]);

                // parse witness and instance variables
                let re = Regex::new(r"W\d+?|I\d+?").unwrap();
                for cap in re.captures_iter(&cap[2]) {
                    match &cap[0].chars().nth(0).unwrap() {
                        'W' => {
                            let com = witness_coms.get(&cap[0]).expect(&format!("missing witness var {}", &cap[0]));
                            assert!(com.0.len() == 1, format!("witness var {} is longer than 32 bytes", &cap[0]));
                            w_scalars.push(com.0[0]);
                            w_variables.push(com.2[0]);
                        },
                        'I' => {
                            let var = instance_vars.get(&cap[0]).expect(&format!("missing instance var {}", &cap[0]));
                            assert!(var.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[0]));
                            i_variables.push(var.to_vec());
                        },
                        _ => panic!("invalid state")
                    }
                }
                
                let gadget = MerkleTree256::new(root, i_variables, pattern.clone());
                let _ = gadget.prove(&mut prover, &w_scalars, &w_variables);
            },
            _ => panic!("unknown gadget: {}", gadget)
        }
    }

    // ---------- CREATE PROOF ----------
    let proof = prover.prove(&bp_gens).unwrap();

    // ---------- WRITE PROOF TO FILE ----------
    let mut file = File::create("test.proof")?;
    file.write_all(&proof.to_bytes())?;

    // ---------- WRITE COMMITMENTS TO FILE ----------
    let mut file = File::create("test.commitments")?;
    for (key, (_, commitments, _)) in witness_coms {
        for (j, commitment) in commitments.iter().enumerate() {
            let o = format!("C{}-{} = 0x{}\n", &key[1..], j, hex::encode(commitment.as_bytes()));
            file.write_all(o.as_bytes())?;
        }
    }

    // ---------- WRITE DERIVED COMMITMENTS TO FILE ----------
    for (key, commitment) in derived_coms {
        let o = format!("{} = 0x{}\n", key, hex::encode(commitment.as_bytes()));
        file.write_all(o.as_bytes())?;
    }

    Ok(())
}