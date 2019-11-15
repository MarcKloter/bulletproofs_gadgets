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
use bulletproofs_gadgets::mimc_hash::mimc::mimc_hash;
use bulletproofs_gadgets::equality::equality_gadget::Equality;
use bulletproofs_gadgets::set_membership::set_membership_gadget::SetMembership;
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

                let a = assignments.get_derived(index, 0, 0);
                let b = assignments.get_derived(index, 1, 0);

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

                let preimage: Vec<Variable> = assignments.get_all_commitments(preimage);

                let derived1 = assignments.get_derived(index, 0, 0);
                let derived2 = assignments.inquire_derived(index, 1, 0);
                let derived_witnesses = if derived2.is_some() { vec![derived1, *derived2.unwrap()] } else { vec![derived1] };

                no_of_bp_gens += (preimage.len() + 1) * 1024;

                let gadget = MimcHash256::new(image);
                gadget.verify(&mut verifier, &preimage, &derived_witnesses);
            },
            GadgetOp::Merkle => {
                let merkle_parser = gadget_grammar::MerkleGadgetParser::new();
                let (root, instance_vars, witness_vars, pattern) = merkle_parser.parse(&line).unwrap();

                let root: LinearCombination = match root {
                    Var::Witness(_) => assignments.get_commitment(root, 0).into(),
                    Var::Instance(_) => be_to_scalar(&assignments.get_instance(root, Some(&assert_32))).into(),
                    _ => panic!("invalid state")
                };

                let instance_vars: Vec<LinearCombination> = instance_vars.into_iter()
                    .map(|var| hash_instance(var, &assignments)).collect();
                
                let mut hash_number = 0;
                let witness_vars: Vec<LinearCombination> = witness_vars.into_iter()
                    .map(|var| {
                        let (image_var, bp_gens) = hash_witness(&mut verifier, var, index, hash_number, &assignments);
                        no_of_bp_gens += bp_gens;
                        hash_number += 1;
                        image_var.into()
                    }).collect();
                
                // add generators for hashes in branches
                no_of_bp_gens += (2 * (witness_vars.len() + instance_vars.len()) - 1) * 2048;
                
                let gadget = MerkleTree256::new(root.into(), instance_vars, witness_vars, pattern.clone());
                gadget.verify(&mut verifier, &Vec::new(), &Vec::new());
            },
            GadgetOp::Equality => {
                let equality_parser = gadget_grammar::EqualityGadgetParser::new();
                let (left, right) = equality_parser.parse(&line).unwrap();

                let left = assignments.get_all_commitments(left);

                let right: Vec<LinearCombination> = match right {
                    Var::Witness(_) => assignments.get_all_commitments(right).into_iter().map(|var| var.into()).collect(),
                    Var::Instance(_) => be_to_scalars(&assignments.get_instance(right, None)).into_iter().map(|scalar| scalar.into()).collect(),
                    _ => panic!("invalid state")
                };

                no_of_bp_gens += left.len();

                let gadget = Equality::new(right);
                gadget.verify(&mut verifier, &left, &Vec::new());
            },
            GadgetOp::Inequality => {
                let inequality_parser = gadget_grammar::InequalityGadgetParser::new();
                let (left, right) = inequality_parser.parse(&line).unwrap();

                let left: Vec<Variable> = assignments.get_all_commitments(left);

                let right_lc: Vec<LinearCombination> = match right {
                    Var::Witness(_) => assignments.get_all_commitments(right).into_iter().map(|var| var.into()).collect(),
                    Var::Instance(_) => be_to_scalars(&assignments.get_instance(right, None)).into_iter().map(|scalar| scalar.into()).collect(),
                    _ => panic!("invalid state")
                };

                let mut derived_witnesses: Vec<Variable> = Vec::new();

                // get delta and delta_inv values
                for i in 0..(left.len() * 2) {
                    derived_witnesses.push(assignments.get_derived(index, i, 0));
                }

                // get sum_inv value
                derived_witnesses.push(assignments.get_derived(index, left.len() * 2, 0));

                no_of_bp_gens += left.len()*4;

                let gadget = Inequality::new(right_lc, None);
                gadget.verify(&mut verifier, &left, &derived_witnesses);
            },
            GadgetOp::SetMembership => {
                let set_membership_parser = gadget_grammar::SetMembershipGadgetParser::new();
                let (member, set) = set_membership_parser.parse(&line).unwrap();
                
                let member_lcs: Vec<LinearCombination> = match member {
                    Var::Witness(_) => assignments.get_all_commitments(member.clone()).into_iter().map(|var| var.into()).collect(),
                    Var::Instance(_) => be_to_scalars(&assignments.get_instance(member.clone(), None)).into_iter().map(|scalar| scalar.into()).collect(),
                    _ => panic!("invalid state")
                };

                let mut member_lc = member_lcs[0].clone();
                let mut apply_hashing = false;

                let mut witness_set_vars = Vec::new();
                let mut instance_set_lcs = Vec::new();
                let mut derived_witnesses: Vec<Variable> = Vec::new();
                let mut derived_pointer = 0;

                if !apply_hashing {
                    for element in set.clone() {
                        match element {
                            Var::Witness(_) => {
                                let witness = assignments.get_all_commitments(element.clone());
                                derived_witnesses.push(assignments.get_derived(index, derived_pointer, 0));
                                derived_pointer += 1;
                                if witness.len() == 1 {
                                    witness_set_vars.push(witness[0]);
                                } else {
                                    apply_hashing = true;
                                }
                            },
                            Var::Instance(_) => {
                                let instance_lcs: Vec<LinearCombination> = be_to_scalars(&assignments.get_instance(element, None)).into_iter().map(|scalar| scalar.into()).collect();
                                if instance_lcs.len() == 1 {
                                    instance_set_lcs.push(instance_lcs[0].clone());
                                } else {
                                    apply_hashing = true;
                                }
                            },
                            _ => panic!("invalid state")
                        }
                    }
                }

                if member_lcs.len() > 1 {
                    apply_hashing = true;
                }

                // get one-hot vector
                for _ in 0..set.len() {
                    derived_witnesses.push(assignments.get_derived(index, derived_pointer, 0));
                    derived_pointer += 1;
                }

                if apply_hashing {
                    let mut hash_number = 1;
                    let hashed_member_lc: LinearCombination = match member {
                        Var::Witness(_) => {
                            let (image_var, bp_gens) = hash_witness(&mut verifier, member, index, hash_number, &assignments);
                            no_of_bp_gens += bp_gens;
                                hash_number += 1;
                            image_var.into()
                        },
                        Var::Instance(_) => hash_instance(member, &assignments),
                        _ => panic!("invalid state")
                    };

                    member_lc = hashed_member_lc;

                    witness_set_vars = Vec::new();
                    instance_set_lcs = Vec::new();            

                    for element in set {
                        match element {
                            Var::Witness(_) => {
                                let (image_var, bp_gens) = hash_witness(&mut verifier, element, index, hash_number, &assignments);
                                no_of_bp_gens += bp_gens;
                                hash_number += 1;
                                witness_set_vars.push(image_var);
                            },
                            Var::Instance(_) => {
                                let image_lc = hash_instance(element, &assignments);
                                instance_set_lcs.push(image_lc);
                            },
                            _ => panic!("invalid state")
                        }
                    }
                }

                no_of_bp_gens += instance_set_lcs.len() * 5 + witness_set_vars.len() * 8;

                let gadget = SetMembership::new(member_lc, None, instance_set_lcs, None);
                gadget.verify(&mut verifier, &witness_set_vars, &derived_witnesses);
            }
        }
    }

    // ---------- VERIFY PROOF ----------
    let bp_gens = BulletproofGens::new(round_pow2(no_of_bp_gens), 1);
    let result = verifier.verify(&proof, &pc_gens, &bp_gens);
    match result {
        Err(_) => println!("false"),
        _ => println!("true")
    }
 
    Ok(())
}

fn hash_witness(
    verifier: &mut Verifier,
    var: Var,
    index: usize,
    subroutine: usize,
    assignments: &Assignments
) -> (Variable, usize) {
    let preimage: Vec<Variable> = assignments.get_all_commitments(var);
    let image = assignments.get_derived(index, 0, subroutine);

    let derived1 = assignments.get_derived(index, 1, subroutine);
    let derived2 = assignments.inquire_derived(index, 2, subroutine);
    let derived_witnesses = if derived2.is_some() { vec![derived1, *derived2.unwrap()] } else { vec![derived1] };

    let gadget = MimcHash256::new(image.into());
    gadget.verify(verifier, &preimage, &derived_witnesses);

    // add generators for hasing
    let no_of_bp_gens = preimage.len() * 2048;
    
    (image, no_of_bp_gens)
}

fn hash_instance(
    var: Var,
    assignments: &Assignments
) -> LinearCombination {
    let instance_var: Vec<u8> = assignments.get_instance(var, None);
    let image = mimc_hash(&instance_var);

    image.into()
}