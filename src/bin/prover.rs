extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
#[macro_use] extern crate bulletproofs_gadgets;
#[macro_use] extern crate lalrpop_util;
extern crate math;

use bulletproofs::r1cs::{Prover, Variable, LinearCombination};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
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
use std::io::{BufReader};
use std::fs::File;
use std::env;
use math::round;

// lalrpop parsers
lalrpop_mod!(gadget_grammar, "/lalrpop/gadget_grammar.rs");

// file extensions
const GADGETS_EXT: &str = ".gadgets";
const PROOF_EXT: &str = ".proof";
const COMMITMENTS_EXT: &str = ".coms";

fn round_pow2(num: usize) -> usize {
    2_usize.pow(round::ceil((num as f64).log2(), 0) as u32)
}

fn main() -> std::io::Result<()> {
    // ---------- COLLECT CMD LINE ARGUMENTS ----------
    let filename = Box::leak(env::args().nth(1).expect("missing argument").into_boxed_str());

    let mut no_of_bp_gens = 0;

    // ---------- CREATE PROVER ----------
    let mut transcript = Transcript::new(filename.as_bytes());
    let pc_gens = PedersenGens::default();
    let mut prover = Prover::new(&pc_gens, &mut transcript);

    let mut assignments = Assignments::new();

    let mut coms_file = File::create(format!("{}{}", filename, COMMITMENTS_EXT))?;
    
    // ---------- PARSE .inst FILE ----------
    assignments.parse_inst(filename.to_string()).expect("unable not read .inst file");
    
    // ---------- PARSE .wtns FILE, WRITE .coms FILE ----------
    assignments.parse_wtns(filename.to_string(), &mut prover, &mut coms_file).expect("could not read .wtns file");

    // ---------- GADGETS ----------
    let file = File::open(format!("{}{}", filename, GADGETS_EXT))?;
    for (index, line) in BufReader::new(file).lines().enumerate() {
        let line = line.unwrap();
        let gadget_op = line.split_whitespace().next().unwrap_or("");

        let error = format!("unknown gadget: {}", &gadget_op);
        match gadget_op.parse::<GadgetOp>().expect(&error) {
            GadgetOp::Bound => {
                let bound_parser = gadget_grammar::BoundGadgetParser::new();
                let (var, min, max) = bound_parser.parse(&line).unwrap();
                
                let var = assignments.get_witness(var, Some(&assert_witness_32));
                let min: Vec<u8> = assignments.get_instance(min, Some(&assert_32));
                let max: Vec<u8> = assignments.get_instance(max, Some(&assert_32));

                no_of_bp_gens += 256;

                let gadget = BoundsCheck::new(&min, &max);
                let coms = gadget.prove(&mut prover, &var.0, &var.2);
                assignments.parse_derived_wtns(coms, index, &mut coms_file).expect("unable to write .coms file");
            },
            GadgetOp::Hash => {
                let hash_parser = gadget_grammar::HashGadgetParser::new();
                let (image, preimage) = hash_parser.parse(&line).unwrap();

                let image: LinearCombination = match image {
                    Var::Witness(_) => assignments.get_witness(image, Some(&assert_witness_32)).2[0].into(),
                    Var::Instance(_) => be_to_scalar(&assignments.get_instance(image, Some(&assert_32))).into(),
                    _ => panic!("invalid state")
                };

                let preimage = assignments.get_witness(preimage, None);

                no_of_bp_gens += (preimage.1.len() + 1) * 512;

                let gadget = MimcHash256::new(image);
                let coms = gadget.prove(&mut prover, &preimage.0, &preimage.2);
                assignments.parse_derived_wtns(coms, index, &mut coms_file).expect("unable to write .coms file");
            },
            GadgetOp::Merkle => {
                let merkle_parser = gadget_grammar::MerkleGadgetParser::new();
                let (root, instance_vars, witness_vars, pattern) = merkle_parser.parse(&line).unwrap();

                let root: LinearCombination = match root {
                    Var::Witness(_) => assignments.get_witness(root, Some(&assert_witness_32)).2[0].into(),
                    Var::Instance(_) => be_to_scalar(&assignments.get_instance(root, Some(&assert_32))).into(),
                    _ => panic!("invalid state")
                };

                let instance_vars: Vec<Vec<u8>> = instance_vars.iter()
                    .map(|var| assignments.get_instance(var.clone(), Some(&assert_32))).collect();
                let (witness_vars, witness_scalars): (Vec<Variable>, Vec<Scalar>) = witness_vars.iter()
                    .map(|var| {
                        let witness = assignments.get_witness(var.clone(), Some(&assert_witness_32));
                        (witness.2[0], witness.0[0])
                    }).unzip();

                no_of_bp_gens += witness_vars.len() * 512;
                no_of_bp_gens += instance_vars.len() * 512;
                
                let gadget = MerkleTree256::new(root, instance_vars, pattern.clone());
                let _ = gadget.prove(&mut prover, &witness_scalars, &witness_vars);
            },
            GadgetOp::Equality => {
                let equality_parser = gadget_grammar::EqualityGadgetParser::new();
                let (left, right) = equality_parser.parse(&line).unwrap();

                let left = assignments.get_witness(left, None);

                let right: Vec<LinearCombination> = match right {
                    Var::Witness(_) => assignments.get_witness(right, None).2.into_iter().map(|var| var.into()).collect(),
                    Var::Instance(_) => be_to_scalars(&assignments.get_instance(right, None)).into_iter().map(|scalar| scalar.into()).collect(),
                    _ => panic!("invalid state")
                };

                no_of_bp_gens += left.1.len();

                let gadget = Equality::new(right);
                let coms = gadget.prove(&mut prover, &left.0, &left.2);
                assignments.parse_derived_wtns(coms, index, &mut coms_file).expect("unable to write .coms file");
            },
            GadgetOp::Inequality => {
                let inequality_parser = gadget_grammar::InequalityGadgetParser::new();
                let (left, right) = inequality_parser.parse(&line).unwrap();

                let left = assignments.get_witness(left, None);

                let (right_scalars, right_lc) = match right {
                    Var::Witness(_) => {
                        let scalars: Vec<Scalar> = assignments.get_witness(right, None).0;
                        let lcs: Vec<LinearCombination> = scalars.clone().into_iter().map(|scalar| scalar.into()).collect();
                        (scalars, lcs)
                    },
                    Var::Instance(_) => {
                        let scalars: Vec<Scalar> = be_to_scalars(&assignments.get_instance(right, None));
                        let lcs: Vec<LinearCombination> = scalars.clone().into_iter().map(|scalar| scalar.into()).collect();
                        (scalars, lcs)
                    },
                    _ => panic!("invalid state")
                };

                no_of_bp_gens += left.1.len()*2;

                let gadget = Inequality::new(right_lc, Some(right_scalars));
                let coms = gadget.prove(&mut prover, &left.0, &left.2);
                assignments.parse_derived_wtns(coms, index, &mut coms_file).expect("unable to write .coms file");
            }
        }
    }
    
    // ---------- CREATE PROOF ----------
    let bp_gens = BulletproofGens::new(round_pow2(no_of_bp_gens), 1);
    let proof = prover.prove(&bp_gens).unwrap();

    // ---------- WRITE PROOF TO FILE ----------
    let mut file = File::create(format!("{}{}", filename, PROOF_EXT))?;
    file.write_all(&proof.to_bytes())?;

    Ok(())
}