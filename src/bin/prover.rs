extern crate curve25519_dalek;
extern crate merlin;
extern crate bulletproofs;
#[macro_use] extern crate bulletproofs_gadgets;
#[macro_use] extern crate lalrpop_util;
extern crate math;

use bulletproofs::r1cs::{Prover, LinearCombination, Variable};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use bulletproofs_gadgets::gadget::Gadget;
use bulletproofs_gadgets::merkle_tree::merkle_tree_gadget::MerkleTree256;
use bulletproofs_gadgets::bounds_check::bounds_check_gadget::BoundsCheck;
use bulletproofs_gadgets::mimc_hash::mimc_hash_gadget::MimcHash256;
use bulletproofs_gadgets::mimc_hash::mimc::mimc_hash;
use bulletproofs_gadgets::equality::equality_gadget::Equality;
use bulletproofs_gadgets::less_than::less_than_gadget::LessThan;
use bulletproofs_gadgets::set_membership::set_membership_gadget::SetMembership;
use bulletproofs_gadgets::inequality::inequality_gadget::Inequality;
use bulletproofs_gadgets::conversions::{be_to_scalar, be_to_scalars, scalar_to_be};
use bulletproofs_gadgets::lalrpop::ast::*;
use bulletproofs_gadgets::lalrpop::assignment_parser::*;
use bulletproofs_gadgets::commitments::commit_single;
use bulletproofs_gadgets::cs_buffer::{ConstraintSystemBuffer, ProverBuffer};
use bulletproofs_gadgets::or::or_conjunction::or;

use std::io::prelude::*;
use std::io::{BufReader, Lines};
use std::iter::{Peekable, Enumerate};
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

    // ---------- CREATE PROVER ----------
    let mut transcript = Transcript::new(filename.as_bytes());
    let pc_gens = PedersenGens::default();
    let mut prover = Prover::new(&pc_gens, &mut transcript);

    // ---------- CREATE BUFFER ----------
    let buffer_gens = PedersenGens::default();
    let mut buffer_transcript = Transcript::new(b"BufferTranscript");
    let buffer_prover = Prover::new(&buffer_gens, &mut buffer_transcript);
    let mut prover_buffer = ProverBuffer::new(buffer_prover);

    let mut assignments = Assignments::new();

    let mut coms_file = File::create(format!("{}{}", filename, COMMITMENTS_EXT))?;
    
    // ---------- PARSE .inst FILE ----------
    assignments.parse_inst(filename.to_string()).expect("unable not read .inst file");
    
    // ---------- PARSE .wtns FILE, WRITE .coms FILE ----------
    assignments.parse_wtns(filename.to_string(), &mut prover, &mut coms_file).expect("could not read .wtns file");

    // ---------- GADGETS ----------
    let file = File::open(format!("{}{}", filename, GADGETS_EXT))?;
    let mut iter = BufReader::new(file).lines().enumerate().into_iter().peekable();
    while iter.peek().is_some() {
        let (index, line) = iter.next().unwrap();
        let line = line.unwrap();

        parse_gadget(&mut iter, &line, &mut assignments, &mut prover, &mut prover_buffer, false, index, &mut coms_file);
    }
    
    // output number of constraints
    println!("{}", prover.num_constraints());

    // ---------- CREATE PROOF ----------
    let bp_gens = BulletproofGens::new(round_pow2(prover.get_num_multiplications()), 1);
    let proof = prover.prove(&bp_gens).unwrap();

    // ---------- WRITE PROOF TO FILE ----------
    let mut file = File::create(format!("{}{}", filename, PROOF_EXT))?;
    file.write_all(&proof.to_bytes())?;

    Ok(())
}

fn parse_gadget(
    iter: &mut Peekable<Enumerate<Lines<BufReader<File>>>>,
    line: &String,
    assignments: &mut Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    match get_gadget_op(line) {
        GadgetOp::Bound => bounds_check_gadget(line, assignments, prover, prover_buffer, buffering, index, coms_file),
        GadgetOp::Hash => mimc_hash_gadget(line, assignments, prover, prover_buffer, buffering, index, coms_file),
        GadgetOp::Merkle => merkle_tree_gadget(line, assignments, prover, prover_buffer, buffering, index, coms_file),
        GadgetOp::Equality => equality_gadget(line, assignments, prover, prover_buffer, buffering),
        GadgetOp::LessThan => less_than_gadget(line, assignments, prover, prover_buffer, buffering, index, coms_file),
        GadgetOp::Inequality => inequality_gadget(line, assignments, prover, prover_buffer, buffering, index, coms_file),
        GadgetOp::SetMembership => set_membership_gadget(line, assignments, prover, prover_buffer, buffering, index, coms_file),
        GadgetOp::Or => or_conjunction(iter, assignments, prover, prover_buffer, buffering, index, coms_file),
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

    let mut depth = 1;

    while iter.peek().is_some() {
        let (_, line) = iter.next().unwrap();
        let line = line.unwrap();
        let gadget_op = get_gadget_op(&line);
        if gadget_op.is_block_end() { clauses.push(block); block = Vec::new(); }
        if gadget_op.is_array_start() { depth = depth - 1; }
        if gadget_op.is_array_end() { depth = depth - 1; }
        if depth == 0 { return clauses; }
        block.push(line);
    }

    panic!("array or code block was opened but never closed");
}

fn hash_witness(
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    var: Var,
    assignments: &mut Assignments,
    index: usize,
    subroutine: usize,
    coms_file: &mut File
) -> (Scalar, Variable) {
    let mut hash_commitments = Vec::new();
    let (preimage_scalars, _, preimage_vars, preimage_bytes) = assignments.get_witness(var, None);
    let image: Scalar = mimc_hash(&preimage_bytes);
    let (image_scalar, image_com, image_var) = commit_single(prover, &scalar_to_be(&image));
    hash_commitments.push(image_com);
    let hash_gadget = MimcHash256::new(image_var.into());
    let (derived_coms, derived_wtns) = hash_gadget.setup(prover, &preimage_scalars);
    if buffering { 
        prover_buffer.commit(&vec![image]);
        prover_buffer.commit_drvd(&derived_wtns);
        hash_gadget.prove(prover_buffer, &preimage_vars, &derived_wtns);
    } else {
        hash_gadget.prove(prover, &preimage_vars, &derived_wtns);
    }
    derived_coms.into_iter().for_each(|com| hash_commitments.push(com));

    assignments.cache_derived_wtns(derived_wtns);
    assignments.parse_derived_wtns(hash_commitments.clone(), index, subroutine, coms_file).expect("unable to write .coms file");
    
    (image_scalar, image_var)
}

fn hash_instance(
    var: Var,
    assignments: &Assignments
) -> (Scalar, LinearCombination) {
    let instance_var: Vec<u8> = assignments.get_instance(var, None);
    let image = mimc_hash(&instance_var);

    (image, image.into())
}

fn or_conjunction(
    iter: &mut Peekable<Enumerate<Lines<BufReader<File>>>>,
    assignments: &mut Assignments,
    prover: &mut Prover,
    parent_prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    let clauses: Vec<Vec<String>> = get_clauses(iter);

    let or_gens = PedersenGens::default();
    let mut or_transcript = Transcript::new(b"OrTranscript");
    let or_prover = Prover::new(&or_gens, &mut or_transcript);
    let mut prover_buffer = ProverBuffer::new(or_prover);
    assignments.buffer_commit_wtns(&mut prover_buffer);
    assignments.buffer_commit_drvd(&mut prover_buffer);

    let mut local_index = index;
    for clause in clauses {
        local_index = local_index + 1;
        for line in clause {
            local_index = local_index + 1;
            parse_gadget(iter, &line, assignments, prover, &mut prover_buffer, true, local_index, coms_file);
        }
        local_index = local_index + 1;

        prover_buffer.rewind();
    }

    if buffering {
        or(parent_prover_buffer, &prover_buffer);
    } else {
        or(prover, &prover_buffer);
    }
}

fn bounds_check_gadget(
    line: &str,
    assignments: &mut Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    let bound_parser = gadget_grammar::BoundGadgetParser::new();
    let (var, min, max) = bound_parser.parse(line).unwrap();
    
    let var = assignments.get_witness(var, Some(&assert_witness_32));
    let min: Vec<u8> = assignments.get_instance(min, Some(&assert_32));
    let max: Vec<u8> = assignments.get_instance(max, Some(&assert_32));

    let gadget = BoundsCheck::new(&min, &max);
    let (derived_coms, derived_wtns) = gadget.setup(prover, &var.0);
    if buffering {
        prover_buffer.commit_drvd(&derived_wtns);
        gadget.prove(prover_buffer, &var.2, &derived_wtns);
    } else {
        gadget.prove(prover, &var.2, &derived_wtns);
    }
    assignments.cache_derived_wtns(derived_wtns);
    assignments.parse_derived_wtns(derived_coms, index, 0, coms_file).expect("unable to write .coms file");
}

fn mimc_hash_gadget(
    line: &str,
    assignments: &mut Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    let hash_parser = gadget_grammar::HashGadgetParser::new();
    let (image, preimage) = hash_parser.parse(line).unwrap();

    let image: LinearCombination = match image {
        Var::Witness(_) => assignments.get_witness(image, Some(&assert_witness_32)).2[0].into(),
        Var::Instance(_) => be_to_scalar(&assignments.get_instance(image, Some(&assert_32))).into(),
        _ => panic!("invalid state")
    };

    let preimage = assignments.get_witness(preimage, None);

    let gadget = MimcHash256::new(image);
    let (derived_coms, derived_wtns) = gadget.setup(prover, &preimage.0);
    
    if buffering {
        prover_buffer.commit_drvd(&derived_wtns);
        gadget.prove(prover_buffer, &preimage.2, &derived_wtns);
    } else {
        gadget.prove(prover, &preimage.2, &derived_wtns);
    }
    assignments.cache_derived_wtns(derived_wtns);
    assignments.parse_derived_wtns(derived_coms, index, 0, coms_file).expect("unable to write .coms file");
}

fn merkle_tree_gadget(
    line: &str,
    assignments: &mut Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    let merkle_parser = gadget_grammar::MerkleGadgetParser::new();
    let (root, instance_vars, witness_vars, pattern) = merkle_parser.parse(line).unwrap();

    let root: LinearCombination = match root {
        Var::Witness(_) => assignments.get_witness(root, Some(&assert_witness_32)).2[0].into(),
        Var::Instance(_) => be_to_scalar(&assignments.get_instance(root, Some(&assert_32))).into(),
        _ => panic!("invalid state")
    };

    let instance_vars: Vec<LinearCombination> = instance_vars.into_iter()
        .map(|var| mimc_hash(&assignments.get_instance(var.clone(), None)).into()).collect();

    let mut hash_number = 0;
    let mut witness_lcs: Vec<LinearCombination> = Vec::new();

    for witness_var in witness_vars {
        let (_, var) = hash_witness(prover, prover_buffer, buffering, witness_var, assignments, index, hash_number, coms_file);
        hash_number += 1;
        witness_lcs.push(var.into());
    }

    let gadget = MerkleTree256::new(root, instance_vars, witness_lcs, pattern.clone());
        
    if buffering {
        gadget.prove(prover_buffer, &Vec::new(), &Vec::new());
    } else {
        gadget.prove(prover, &Vec::new(), &Vec::new());
    }
}

fn equality_gadget(
    line: &str,
    assignments: &Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool
) {
    let equality_parser = gadget_grammar::EqualityGadgetParser::new();
    let (left, right) = equality_parser.parse(line).unwrap();

    let (_, _, left_vars, _)  = assignments.get_witness(left, None);

    let right: Vec<LinearCombination> = match right {
        Var::Witness(_) => assignments.get_witness(right, None).2.into_iter().map(|var| var.into()).collect(),
        Var::Instance(_) => be_to_scalars(&assignments.get_instance(right, None)).into_iter().map(|scalar| scalar.into()).collect(),
        _ => panic!("invalid state")
    };
    
    let gadget = Equality::new(right);
    
    if buffering {
        gadget.prove(prover_buffer, &left_vars, &Vec::new());
    } else {
        gadget.prove(prover, &left_vars, &Vec::new());
    }
}

fn less_than_gadget(
    line: &str,
    assignments: &mut Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    let less_than_parser = gadget_grammar::LessThanGadgetParser::new();
    let (left, right) = less_than_parser.parse(line).unwrap();

    let (left_scalars, _, left_vars, _) = assignments.get_witness(left, Some(&assert_witness_32));
    let (right_scalars, _, right_vars, _) = assignments.get_witness(right, Some(&assert_witness_32));

    let gadget = LessThan::new(left_vars[0].into(), Some(left_scalars[0]), right_vars[0].into(), Some(right_scalars[0]));
    let (derived_coms, derived_wtns) = gadget.setup(prover, &Vec::new());
    if buffering {
        prover_buffer.commit_drvd(&derived_wtns);
        gadget.prove(prover_buffer, &Vec::new(), &derived_wtns);
    } else {
        gadget.prove(prover, &Vec::new(), &derived_wtns);
    }
    assignments.cache_derived_wtns(derived_wtns);
    assignments.parse_derived_wtns(derived_coms, index, 0, coms_file).expect("unable to write .coms file");
}

fn inequality_gadget(
    line: &str,
    assignments: &mut Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    let inequality_parser = gadget_grammar::InequalityGadgetParser::new();
    let (left, right) = inequality_parser.parse(line).unwrap();

    let left = assignments.get_witness(left, None);

    let (right_scalars, right_lc) = match right {
        Var::Witness(_) => {
            let (scalars, _, vars, _) = assignments.get_witness(right, None);
            let lcs: Vec<LinearCombination> = vars.into_iter().map(|var| var.into()).collect();
            (scalars, lcs)
        },
        Var::Instance(_) => {
            let scalars: Vec<Scalar> = be_to_scalars(&assignments.get_instance(right, None));
            let lcs: Vec<LinearCombination> = scalars.clone().into_iter().map(|scalar| scalar.into()).collect();
            (scalars, lcs)
        },
        _ => panic!("invalid state")
    };
    
    let gadget = Inequality::new(right_lc, Some(right_scalars));
    let (derived_coms, derived_wtns) = gadget.setup(prover, &left.0);
    if buffering {
        prover_buffer.commit_drvd(&derived_wtns);
        gadget.prove(prover_buffer, &left.2, &derived_wtns);
    } else {
        gadget.prove(prover, &left.2, &derived_wtns);
    }
    assignments.cache_derived_wtns(derived_wtns);
    assignments.parse_derived_wtns(derived_coms, index, 0, coms_file).expect("unable to write .coms file");
}

fn set_membership_gadget(
    line: &str,
    assignments: &mut Assignments,
    prover: &mut Prover,
    prover_buffer: &mut ProverBuffer,
    buffering: bool,
    index: usize,
    coms_file: &mut File
) {
    let set_membership_parser = gadget_grammar::SetMembershipGadgetParser::new();
    let (member, set) = set_membership_parser.parse(&line).unwrap();

    let (member_scalars, member_lcs): (Vec<Scalar>, Vec<LinearCombination>) = match member.clone() {
        Var::Witness(_) => {
            let (witness_scalars, _, witness_vars, _)  = assignments.get_witness(member.clone(), None);
            let linear_combinations = witness_vars.into_iter().map(|var| var.into()).collect();
            (witness_scalars, linear_combinations)
        },
        Var::Instance(_) => {
            let member_assignments: Vec<Scalar> = be_to_scalars(&assignments.get_instance(member.clone(), None));
            let linear_combinations = member_assignments.clone().into_iter().map(|scalar| scalar.into()).collect();
            (member_assignments, linear_combinations)
        },
        _ => panic!("invalid state")
    };

    let mut member_scalar: Scalar = member_scalars[0];
    let mut member_lc: LinearCombination = member_lcs[0].clone();

    let mut apply_hashing = member_scalars.len() > 1;

    let mut witness_set_vars = Vec::new();
    let mut witness_set_scalars = Vec::new();

    let mut instance_set_lcs = Vec::new();
    let mut instance_set_scalars = Vec::new();

    if !apply_hashing {
        for element in set.clone() {
            match element {
                Var::Witness(_) => { 
                    let (witness_scalar, _, witness_var, _) = assignments.get_witness(element, None);
                    if witness_var.len() == 1 {
                        witness_set_scalars.push(witness_scalar[0]);
                        witness_set_vars.push(witness_var[0]);
                    } else {
                        apply_hashing = true;
                    }
                },
                Var::Instance(_) => {
                    let instance_scalars = be_to_scalars(&assignments.get_instance(element, None));
                    if instance_scalars.len() == 1 {
                        instance_set_scalars.push(instance_scalars[0]);
                        instance_set_lcs.push(instance_scalars[0].into());
                    } else {
                        apply_hashing = true;
                    }
                },
                _ => panic!("invalid state")
            };
        }
    }

    // if there are set elements that exceed one scalar, use hashing to avoid knowledge leaking
    if apply_hashing {
        let mut hash_number = 1;
        let (scalar, lc) = match member {
            Var::Witness(_) => {
                let (scalar, var) = hash_witness(prover, prover_buffer, buffering, member, assignments, index, hash_number, coms_file);    
                hash_number += 1;
                (scalar, var.into())
            },
            Var::Instance(_) => hash_instance(member, &assignments),
            _ => panic!("invalid state")
        };
        member_scalar = scalar;
        member_lc = lc;

        witness_set_vars = Vec::new();
        witness_set_scalars = Vec::new();

        instance_set_lcs = Vec::new();
        instance_set_scalars = Vec::new();

        for element in set {
            match element {
                Var::Witness(_) => {
                    let (scalar, var) = hash_witness(prover, prover_buffer, buffering, element, assignments, index, hash_number, coms_file);
                    hash_number += 1;
                    witness_set_vars.push(var);
                    witness_set_scalars.push(scalar);
                },
                Var::Instance(_) => {
                    let (scalar, lc) = hash_instance(element, &assignments);
                    instance_set_lcs.push(lc);
                    instance_set_scalars.push(scalar);
                },
                _ => panic!("invalid state")
            };
        }
    }

    let gadget = SetMembership::new(member_lc, Some(member_scalar), instance_set_lcs.clone(), Some(instance_set_scalars));
    let (derived_coms, derived_wtns) = gadget.setup(prover, &witness_set_scalars);
    if buffering {
        prover_buffer.commit_drvd(&derived_wtns);
        gadget.prove(prover_buffer, &witness_set_vars, &derived_wtns);
    } else {
        gadget.prove(prover, &witness_set_vars, &derived_wtns);
    }
    assignments.cache_derived_wtns(derived_wtns);
    assignments.parse_derived_wtns(derived_coms, index, 0, coms_file).expect("unable to write .coms file");
}
