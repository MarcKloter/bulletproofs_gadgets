extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
#[macro_use] extern crate bulletproofs_gadgets;
#[macro_use] extern crate lalrpop_util;
extern crate regex;
extern crate math;

use bulletproofs::r1cs::{Verifier, Variable, R1CSProof, LinearCombination, ConstraintSystem};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs_gadgets::gadget::Gadget;
use bulletproofs_gadgets::merkle_tree::merkle_tree_gadget::MerkleTree256;
use bulletproofs_gadgets::bounds_check::bounds_check_gadget::BoundsCheck;
use bulletproofs_gadgets::mimc_hash::mimc_hash_gadget::MimcHash256;
use bulletproofs_gadgets::mimc_hash::mimc::mimc_hash;
use bulletproofs_gadgets::equality::equality_gadget::Equality;
use bulletproofs_gadgets::set_membership::set_membership_gadget::SetMembership;
use bulletproofs_gadgets::less_than::less_than_gadget::LessThan;
use bulletproofs_gadgets::inequality::inequality_gadget::Inequality;
use bulletproofs_gadgets::conversions::{be_to_scalar, be_to_scalars};
use bulletproofs_gadgets::lalrpop::ast::*;
use bulletproofs_gadgets::lalrpop::assignment_parser::*;
use bulletproofs_gadgets::cs_buffer::{ConstraintSystemBuffer, VerifierBuffer};
use bulletproofs_gadgets::or::or_conjunction::or;

use std::io::prelude::*;
use std::io::{BufReader, Lines};
use std::iter::{Peekable, Enumerate};
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
    let mut iter = BufReader::new(file).lines().enumerate().into_iter().peekable();
    while iter.peek().is_some() {
        let (index, line) = iter.next().unwrap();
        let line = line.unwrap();

        parse_gadget(&mut iter, &line, &assignments, &mut verifier, index);
    }

    // ---------- VERIFY PROOF ----------
    let bp_gens = BulletproofGens::new(round_pow2(verifier.get_num_vars()), 1);
    let result = verifier.verify(&proof, &pc_gens, &bp_gens);
    match result {
        Err(_) => {
            println!("false");
            std::process::exit(1)
        },
        _ => {
            println!("true");
            std::process::exit(0)
        }
    }
}

fn parse_gadget(
    iter: &mut Peekable<Enumerate<Lines<BufReader<File>>>>,
    line: &String,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {
    match get_gadget_op(line) {
        GadgetOp::Bound => bounds_check_gadget(line, assignments, verifier, index),
        GadgetOp::Hash => mimc_hash_gadget(line, assignments, verifier, index),
        GadgetOp::Merkle => merkle_tree_gadget(line, assignments, verifier, index),
        GadgetOp::Equality => equality_gadget(line, assignments, verifier),
        GadgetOp::LessThan => less_than_gadget(line, assignments, verifier, index),
        GadgetOp::Inequality => inequality_gadget(line, assignments, verifier, index),
        GadgetOp::SetMembership => set_membership_gadget(line, assignments, verifier, index),
        GadgetOp::Or => or_conjunction(iter, assignments, verifier, index),
        _ => {}
    }
}

fn get_gadget_op(line: &String) -> GadgetOp {
    let gadget_op = line.split_whitespace().next().unwrap_or("");
    let error = format!("unknown gadget: {}", &gadget_op);
    gadget_op.parse::<GadgetOp>().expect(&error)
}

fn get_clauses(
    iter: &mut Peekable<Enumerate<Lines<BufReader<File>>>>
) -> Vec<Vec<String>> {
    let mut clauses = Vec::new();
    let mut block = Vec::new();

    if iter.peek().is_none() {
        panic!("unexpected end of input");
    }

    let mut depth = 0;

    while iter.peek().is_some() {
        let (_, line) = iter.next().unwrap();
        let line = line.unwrap();
        let gadget_op = get_gadget_op(&line);
        if gadget_op.is_block_end() { clauses.push(block); block = Vec::new(); }
        if gadget_op.is_array_start() { depth = depth + 1; }
        if gadget_op.is_array_end() { depth = depth - 1; }
        if depth == 0 { return clauses; }
        block.push(line);
    }

    panic!("array or code block was opened but never closed");
}

fn or_conjunction(
    iter: &mut Peekable<Enumerate<Lines<BufReader<File>>>>,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {
    let clauses: Vec<Vec<String>> = get_clauses(iter);

    let mut or_transcript = Transcript::new(b"OrTranscript");
    let or_verifier = Verifier::new(&mut or_transcript);
    let mut verifier_buffer = VerifierBuffer::new(or_verifier);

    let mut local_index = index + 1;
    for clause in clauses {
        for line in clause {
            parse_gadget(iter, &line, assignments, &mut verifier_buffer, local_index);
            local_index = local_index + 1;
        }
        verifier_buffer.rewind();
    }

    or(verifier, &verifier_buffer);
}

fn bounds_check_gadget(
    line: &str,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {
    let bound_parser = gadget_grammar::BoundGadgetParser::new();
    let (var, min, max) = bound_parser.parse(&line).unwrap();
    
    let var = assignments.get_commitment(var, 0);
    let min: Vec<u8> = assignments.get_instance(min, Some(&assert_32));
    let max: Vec<u8> = assignments.get_instance(max, Some(&assert_32));

    let a = assignments.get_derived(index, 0, 0);
    let b = assignments.get_derived(index, 1, 0);

    let gadget = BoundsCheck::new(&min, &max);
    gadget.verify(verifier, &vec![var], &vec![a, b]);
}

fn mimc_hash_gadget(
    line: &str,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {
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

    let gadget = MimcHash256::new(image);
    gadget.verify(verifier, &preimage, &derived_witnesses);
}

fn merkle_tree_gadget(
    line: &str,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {
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
            let image_var = hash_witness(verifier, var, index, hash_number, &assignments);
            hash_number += 1;
            image_var.into()
        }).collect();
    
    let gadget = MerkleTree256::new(root.into(), instance_vars, witness_vars, pattern.clone());
    gadget.verify(verifier, &Vec::new(), &Vec::new());
}

fn equality_gadget(
    line: &str,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem
) {
    let equality_parser = gadget_grammar::EqualityGadgetParser::new();
    let (left, right) = equality_parser.parse(&line).unwrap();
    
    let left = assignments.get_all_commitments(left);
    
    let right: Vec<LinearCombination> = match right {
        Var::Witness(_) => assignments.get_all_commitments(right).into_iter().map(|var| var.into()).collect(),
        Var::Instance(_) => be_to_scalars(&assignments.get_instance(right, None)).into_iter().map(|scalar| scalar.into()).collect(),
        _ => panic!("invalid state")
    };
    
    let gadget = Equality::new(right);
    gadget.verify(verifier, &left, &Vec::new());
}

fn less_than_gadget(
    line: &str,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {
    let less_than_parser = gadget_grammar::LessThanGadgetParser::new();
    let (left, right) = less_than_parser.parse(&line).unwrap();
    
    let left = assignments.get_commitment(left, 0);
    let right = assignments.get_commitment(right, 0);
    
    let delta = assignments.get_derived(index, 0, 0);
    let delta_inv = assignments.get_derived(index, 1, 0);
    
    let gadget = LessThan::new(left.into(), None, right.into(), None);
    gadget.verify(verifier, &Vec::new(), &vec![delta, delta_inv]);
}

fn inequality_gadget(
    line: &str,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {
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
    
    let gadget = Inequality::new(right_lc, None);
    gadget.verify(verifier, &left, &derived_witnesses);
}

fn set_membership_gadget(
    line: &str,
    assignments: &Assignments,
    verifier: &mut dyn ConstraintSystem,
    index: usize
) {  
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

    if !apply_hashing {
        for element in set.clone() {
            match element {
                Var::Witness(_) => {
                    let witness = assignments.get_all_commitments(element.clone());
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
    for derived_pointer in 0..set.len() {
        derived_witnesses.push(assignments.get_derived(index, derived_pointer, 0));
    }

    if apply_hashing {
        let mut hash_number = 1;
        let hashed_member_lc: LinearCombination = match member {
            Var::Witness(_) => {
                let image_var = hash_witness(verifier, member, index, hash_number, &assignments);
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
                    let image_var = hash_witness(verifier, element, index, hash_number, &assignments);
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

    let gadget = SetMembership::new(member_lc, None, instance_set_lcs, None);
    gadget.verify(verifier, &witness_set_vars, &derived_witnesses);
}

fn hash_witness(
    verifier: &mut dyn ConstraintSystem,
    var: Var,
    index: usize,
    subroutine: usize,
    assignments: &Assignments
) -> Variable {
    let preimage: Vec<Variable> = assignments.get_all_commitments(var);
    let image = assignments.get_derived(index, 0, subroutine);

    let derived1 = assignments.get_derived(index, 1, subroutine);
    let derived2 = assignments.inquire_derived(index, 2, subroutine);
    let derived_witnesses = if derived2.is_some() { vec![derived1, *derived2.unwrap()] } else { vec![derived1] };

    let gadget = MimcHash256::new(image.into());
    gadget.verify(verifier, &preimage, &derived_witnesses);

    image
}

fn hash_instance(
    var: Var,
    assignments: &Assignments
) -> LinearCombination {
    let instance_var: Vec<u8> = assignments.get_instance(var, None);
    let image = mimc_hash(&instance_var);

    image.into()
}