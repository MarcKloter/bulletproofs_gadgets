extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
#[macro_use] extern crate bulletproofs_gadgets;
#[macro_use] extern crate lalrpop_util;
extern crate regex;
extern crate math;

use bulletproofs::r1cs::{Verifier, Variable, R1CSProof, LinearCombination};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs_gadgets::gadget::Gadget;
use bulletproofs_gadgets::merkle_tree::merkle_tree_gadget::MerkleTree256;
use bulletproofs_gadgets::bounds_check::bounds_check_gadget::BoundsCheck;
use bulletproofs_gadgets::mimc_hash::mimc_hash_gadget::MimcHash256;
use bulletproofs_gadgets::equality::equality_gadget::Equality;
use bulletproofs_gadgets::inequality::inequality_gadget::Inequality;
use bulletproofs_gadgets::conversions::{be_to_scalar, be_to_scalars};
use bulletproofs_gadgets::lalrpop::ast::*;
use bulletproofs_gadgets::lalrpop::assignment_parser::*;

use std::io::prelude::*;
use std::io::BufReader;
use std::fs::File;
use std::env;
use std::panic;
use math::round;

// lalrpop parsers
lalrpop_mod!(gadget_grammar, "/lalrpop/gadget_grammar.rs");

// file extensions
const GADGETS_EXT: &str = ".gadgets";
const PROOF_EXT: &str = ".proof";

fn round_pow2(num: usize) -> usize {
    2_usize.pow(round::ceil((num as f64).log2(), 0) as u32)
}

fn main() -> std::io::Result<()> {
    // ---------- COLLECT CMD LINE ARGUMENTS ----------
    let filename = Box::leak(env::args().nth(1).expect("missing argument").into_boxed_str());

    let mut no_of_bp_gens = 0;

    // ---------- CREATE VERIFIER ----------
    let mut verifier_transcript = Transcript::new(filename.as_bytes());
    let pc_gens = PedersenGens::default();
    let mut verifier = Verifier::new(&mut verifier_transcript);

    // ---------- PRASE .proof FILE ----------
    let mut file = File::open(format!("{}{}", filename, PROOF_EXT))?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    let proof = R1CSProof::from_bytes(&buffer[..]).unwrap();

    let mut assignments = Assignments::new();

    // ---------- PARSE .inst FILE ----------
    assignments.parse_inst(filename.to_string()).expect("unable not read .inst file");

    // ---------- PARSE .coms FILE ----------
    assignments.parse_coms(filename.to_string(), &mut verifier).expect("unable not read .coms file");

    // ---------- PARSE .gadgets FILE ----------
    let file = File::open(format!("{}{}", filename, GADGETS_EXT))?;
    for (index, line) in BufReader::new(file).lines().enumerate() {
        let line = line.unwrap();
        let gadget_op = line.split_whitespace().next().unwrap_or("");

        let error = format!("unknown gadget: {}", &gadget_op);
        match gadget_op.parse::<GadgetOp>().expect(&error) {
            GadgetOp::Bound => {
                let bound_parser = gadget_grammar::BoundGadgetParser::new();
                let (var, min, max) = bound_parser.parse(&line).unwrap();
                
                let var = assignments.get_commitment(var, 0);
                let min: Vec<u8> = assignments.get_instance(min, Some(&assert_32));
                let max: Vec<u8> = assignments.get_instance(max, Some(&assert_32));

                let a = assignments.get_derived(index, 0);
                let b = assignments.get_derived(index, 1);

                no_of_bp_gens += 256;

                let gadget = BoundsCheck::new(&min, &max);
                gadget.verify(&mut verifier, &vec![var], &vec![a, b]);
            },
            GadgetOp::Hash => {
                let hash_parser = gadget_grammar::HashGadgetParser::new();
                let (image, preimage) = hash_parser.parse(&line).unwrap();

                let image: LinearCombination = match image {
                    Var::Witness(_) => assignments.get_commitment(image, 0).into(),
                    Var::Instance(_) => be_to_scalar(&assignments.get_instance(image, Some(&assert_32))).into(),
                    _ => panic!("invalid state")
                };

                let mut preimage: Vec<Variable> = assignments.get_all_commitments(preimage);

                let padded_block = assignments.get_derived(index, 0);
                let padding = assignments.get_derived(index, 1);

                no_of_bp_gens += (preimage.len() + 1) * 512;

                let gadget = MimcHash256::new(image);
                gadget.verify(&mut verifier, &preimage, &vec![padded_block, padding]);
            },
            GadgetOp::Merkle => {
                let merkle_parser = gadget_grammar::MerkleGadgetParser::new();
                let (root, instance_vars, witness_vars, pattern) = merkle_parser.parse(&line).unwrap();

                let root: LinearCombination = match root {
                    Var::Witness(_) => assignments.get_commitment(root, 0).into(),
                    Var::Instance(_) => be_to_scalar(&assignments.get_instance(root, Some(&assert_32))).into(),
                    _ => panic!("invalid state")
                };

                let instance_vars: Vec<Vec<u8>> = instance_vars.iter()
                    .map(|var| assignments.get_instance(var.clone(), Some(&assert_32))).collect();
                let witness_vars: Vec<Variable> = witness_vars.iter()
                    .map(|var| assignments.get_commitment(var.clone(), 0)).collect();

                no_of_bp_gens += witness_vars.len() * 512;
                no_of_bp_gens += instance_vars.len() * 512;
                
                let gadget = MerkleTree256::new(root.into(), instance_vars, pattern.clone());
                gadget.verify(&mut verifier, &witness_vars, &Vec::new());
            },
            GadgetOp::Equality => {
                let equality_parser = gadget_grammar::EqualityGadgetParser::new();
                let (left, right) = equality_parser.parse(&line).unwrap();

                let left = assignments.get_all_commitments(left);

                let right: Vec<LinearCombination> = match right {
                    Var::Witness(_) => assignments.get_all_commitments(right).into_iter().map(|var| var.into()).collect(),
                    Var::Instance(_) => be_to_scalars(&assignments.get_instance(right, None)).into_iter().map(|var| var.into()).collect(),
                    _ => panic!("invalid state")
                };

                no_of_bp_gens += left.len();

                let gadget = Equality::new(right);
                gadget.verify(&mut verifier, &left, &Vec::new());
            },
            GadgetOp::Inequality => {
                let inequality_parser = gadget_grammar::InequalityGadgetParser::new();
                let (left, right) = inequality_parser.parse(&line).unwrap();

                let left = assignments.get_all_commitments(left);

                let right: Vec<LinearCombination> = match right {
                    Var::Witness(_) => assignments.get_all_commitments(right).into_iter().map(|var| var.into()).collect(),
                    Var::Instance(_) => be_to_scalars(&assignments.get_instance(right, None)).into_iter().map(|var| var.into()).collect(),
                    _ => panic!("invalid state")
                };

                let mut derived_witnesses: Vec<Variable> = Vec::new();

                // get delta_inv values
                for i in 0..left.len() {
                    derived_witnesses.push(assignments.get_derived(index, i));
                }

                // get sum_inv value
                derived_witnesses.push(assignments.get_derived(index, left.len()));

                no_of_bp_gens += left.len();

                let gadget = Inequality::new(right, None);
                gadget.verify(&mut verifier, &left, &derived_witnesses);
            }
        }
    }

    // ---------- VERIFY PROOF ----------
    let bp_gens = BulletproofGens::new(round_pow2(no_of_bp_gens), 1);
    assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());

    Ok(())
}