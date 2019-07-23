extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
#[macro_use]
extern crate bulletproofs_gadgets;
extern crate regex;
extern crate math;

use bulletproofs::r1cs::{Verifier, Variable, R1CSProof, LinearCombination};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;
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
use math::round;

// file extensions
const INSTANCE_VARS_EXT: &str = ".inst";
const GADGETS_EXT: &str = ".gadgets";
const PROOF_EXT: &str = ".proof";
const COMMITMENTS_EXT: &str = ".coms";

fn round_pow2(num: usize) -> usize {
    2_usize.pow(round::ceil((num as f64).log2(), 0) as u32)
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
    // ---------- COLLECT CMD LINE ARGUMENTS ----------
    let filename = Box::leak(env::args().nth(1).expect("missing argument").into_boxed_str());

    let mut no_of_bp_gens = 0;

    // ---------- CREATE VERIFIER ----------
    let mut verifier_transcript = Transcript::new(filename.as_bytes());
    let pc_gens = PedersenGens::default();
    let mut verifier = Verifier::new(&mut verifier_transcript);

    // ---------- READ PROOF ----------
    let mut file = File::open(format!("{}{}", filename, PROOF_EXT))?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    
    let proof = R1CSProof::from_bytes(&buffer[..]).unwrap();

    // ---------- READ INSTANCE VARS ----------
    let mut instance_vars: HashMap<String, Vec<u8>> = HashMap::new();
    let file = File::open(format!("{}{}", filename, INSTANCE_VARS_EXT))?;
    for line in BufReader::new(file).lines() {
        let string = line.unwrap();
        let re = Regex::new(r"^(I\d+?) = 0x([[:alnum:]]+?)$").unwrap();
        assert!(re.is_match(&string), format!("invalid assignment entry: {}", string));

        let cap = re.captures(&string).unwrap();
        let bytes = hex::decode(&cap[2]).unwrap();
        instance_vars.insert(cap[1].to_string(), bytes);
    }

    // ---------- READ COMMITMENTS ----------
    let mut commitments: HashMap<String, Variable> = HashMap::new();

    let file = File::open(format!("{}{}", filename, COMMITMENTS_EXT))?;
    for line in BufReader::new(file).lines() {
        let string = line.unwrap();
        let re = Regex::new(r"^([C|D]{1}[\d|-]+?) = 0x([[:alnum:]]+?)$").unwrap();
        assert!(re.is_match(&string), format!("invalid commitment entry: {}", string));
        
        let cap = re.captures(&string).unwrap();
        let bytes = hex::decode(&cap[2]).unwrap();
        let com = CompressedRistretto::from_slice(&bytes);
        commitments.insert(cap[1].to_string(), verifier.commit(com));
    }

    // ---------- GADGETS ----------
    let file = File::open(format!("{}{}", filename, GADGETS_EXT))?;
    for (index, line) in BufReader::new(file).lines().enumerate() {
        let string = line.unwrap();
        let re = Regex::new(r"^([[:alnum:]]+?) (.*)$").unwrap();
        assert!(re.is_match(&string), format!("invalid gadget entry: {}", string));
        
        let cap = re.captures(&string).unwrap();
        let gadget = cap[1].to_string();
        let args = &cap[2];

        match gadget.as_ref() {
            "BOUND" => {
                let re = Regex::new(r"^W(\d+?) (I\d+?) (I\d+?)$").unwrap();
                assert!(re.is_match(&args), format!("invalid BOUND arguments: {}", args));
                let cap = re.captures(&args).unwrap();
                
                let val = commitments.get(&format!("C{}-0", &cap[1])).expect(&format!("missing commitment C{}-0", &cap[1]));

                let min: Vec<u8> = instance_vars.get(&cap[2]).expect(&format!("missing instance var {}", &cap[2])).to_vec();
                assert!(min.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[2]));
                let max: Vec<u8> = instance_vars.get(&cap[3]).expect(&format!("missing instance var {}", &cap[3])).to_vec();
                assert!(max.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[3]));

                let a = commitments.get(&format!("D{}-0", index)).expect(&format!("missing commitment D{}-0", index));
                let b = commitments.get(&format!("D{}-1", index)).expect(&format!("missing commitment D{}-1", index));

                no_of_bp_gens += 16;

                let gadget = BoundsCheck::new(&min, &max);
                gadget.verify(&mut verifier, &vec![*val], &vec![*a, *b]);
            },
            "HASH"  => {
                let re = Regex::new(r"^([W|I]{1})(\d+?) W(\d+?)$").unwrap();
                assert!(re.is_match(&args), format!("invalid HASH arguments: {}", args));
                let cap = re.captures(&args).unwrap();

                let image: LinearCombination = match cap[1].to_string().as_ref() {
                    "W" => {
                        let com = *commitments.get(&format!("C{}-0", &cap[2])).expect(&format!("missing commitment C{}-0", &cap[2]));
                        com.into()
                    },
                    "I" => {
                        let inst = instance_vars.get(&format!("I{}", &cap[2])).expect(&format!("missing instance var I{}", &cap[2]));
                        assert!(inst.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[1]));
                        be_to_scalar(inst).into()
                    },
                    _ => panic!("invalid state")
                };

                let mut preimage: Vec<Variable> = Vec::new();
                let mut i = 0;
                while commitments.contains_key(&format!("C{}-{}", &cap[3], i)) {
                    preimage.push(*commitments.get(&format!("C{}-{}", &cap[3], i)).expect(&format!("missing witness var {}", &cap[3])));
                    i += 1;
                }

                let padded_block = commitments.get(&format!("D{}-0", index)).expect(&format!("missing commitment D{}-0", index));
                let padding = commitments.get(&format!("D{}-1", index)).expect(&format!("missing commitment D{}-1", index));

                no_of_bp_gens += (preimage.len() + 1) * 512;

                let gadget = MimcHash256::new(image);
                gadget.verify(&mut verifier, &preimage, &vec![*padded_block, *padding]);
            },
            "MERKLE" => {
                let re = Regex::new(r"^([W|I]{1})(\d+?) (.*)$").unwrap();
                assert!(re.is_match(&args), format!("invalid MERKLE arguments: {}", args));
                let cap = re.captures(&args).unwrap();

                let root: LinearCombination = match cap[1].to_string().as_ref() {
                    "W" => {
                        let com = *commitments.get(&format!("C{}-0", &cap[2])).expect(&format!("missing commitment C{}-0", &cap[2]));
                        com.into()
                    },
                    "I" => {
                        let inst = instance_vars.get(&format!("I{}", &cap[2])).expect(&format!("missing instance var I{}", &cap[2]));
                        assert!(inst.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[1]));
                        be_to_scalar(inst).into()
                    },
                    _ => panic!("invalid state")
                };

                let mut w_variables: Vec<Variable> = Vec::new();
                let mut i_variables: Vec<Vec<u8>> = Vec::new();

                // parse pattern
                let re = Regex::new(r"\(|\)|W|I").unwrap();
                let mut brackets = Vec::new();
                for cap in re.captures_iter(&cap[3]) {
                    brackets.push(cap[0].to_string());
                }
                let pattern = parse(&brackets[..]);

                // parse witness and instance variables
                let re = Regex::new(r"W\d+?|I\d+?").unwrap();
                for cap in re.captures_iter(&cap[3]) {
                    match &cap[0].chars().nth(0).unwrap() {
                        'W' => {
                            let com = commitments.get(&format!("C{}-0", &cap[0][1..])).expect(&format!("missing commitment C{}-0", &cap[0][1..]));
                            w_variables.push(*com);
                        },
                        'I' => {
                            let var = instance_vars.get(&cap[0]).expect(&format!("missing instance var {}", &cap[0]));
                            assert!(var.len() <= 32, format!("instance var {} is longer than 32 bytes", &cap[0]));
                            i_variables.push(var.to_vec());
                        },
                        _ => panic!("invalid state")
                    }
                }

                no_of_bp_gens += w_variables.len() * 512;
                no_of_bp_gens += i_variables.len() * 512;
                
                let gadget = MerkleTree256::new(root.into(), i_variables, pattern.clone());
                gadget.verify(&mut verifier, &w_variables, &Vec::new());
            },
            _ => panic!("unknown gadget: {}", gadget)
        }
    }

    // ---------- VERIFY PROOF ----------
    let bp_gens = BulletproofGens::new(round_pow2(no_of_bp_gens), 1);
    assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());

    Ok(())
}