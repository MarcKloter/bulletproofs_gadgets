use bulletproofs::r1cs::{ConstraintSystem, LinearCombination};
use curve25519_dalek::scalar::Scalar;
use cs_buffer::{ConstraintSystemBuffer, Operation};

pub fn or(main: &mut dyn ConstraintSystem, buffer: &dyn ConstraintSystemBuffer) {
    let mut constraints_vec: Vec<Vec<LinearCombination>> = Vec::new();
    for operations in buffer.buffer_cache() {
        let mut constraints: Vec<LinearCombination> = Vec::new();

        for operation in operations {
            match operation {
                Operation::Multiply((left, right)) => {
                    main.multiply(left.clone(), right.clone());
                },
                Operation::AllocateMultiplier(assignment) => { 
                    assert!(main.allocate_multiplier(assignment.clone()).is_ok());
                },
                Operation::Constrain(lc) => {
                    constraints.push(lc.clone());
                },
                Operation::Commit(_) => {
                    // nop, this was already committed to main
                }
            }
        }

        constraints_vec.push(constraints);
    }

    let cartesian_product: Vec<Vec<LinearCombination>> = cartesian_product(constraints_vec);
    for constraints in cartesian_product { 
        let mut constraint_product: LinearCombination = Scalar::one().into();
        for constraint in constraints {
            let (_, _, product) = main.multiply(constraint_product.clone(), constraint.clone());
            constraint_product = product.into();
        }
        main.constrain(constraint_product); 
    }
}

/// Computes the Cartesian product of lists[0] * lists[1] * ... * lists[n].
/// from: https://gist.github.com/kylewlacy/115965b40e02a3325558
fn partial_cartesian<T: Clone>(a: Vec<Vec<T>>, b: Vec<T>) -> Vec<Vec<T>> {
    a.into_iter().flat_map(|xs| {
        b.iter().cloned().map(|y| {
            let mut vec = xs.clone();
            vec.push(y);
            vec
        }).collect::<Vec<_>>()
    }).collect()
}

/// Computes the Cartesian product of lists[0] * lists[1] * ... * lists[n].
/// from: https://gist.github.com/kylewlacy/115965b40e02a3325558
fn cartesian_product<T: Clone>(lists: Vec<Vec<T>>) -> Vec<Vec<T>> {
    match lists.split_first() {
        Some((first, rest)) => {
            let init: Vec<Vec<T>> = first.iter().cloned().map(|n| vec![n]).collect();

            rest.iter().cloned().fold(init, |vec, list| {
                partial_cartesian(vec, list)
            })
        },
        None => {
            vec![]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use commitments::{commit, verifier_commit};
    use mimc_hash::mimc_hash_gadget::MimcHash256;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use conversions::{be_to_scalar};
    use bulletproofs::r1cs::{Prover, Verifier, Variable};
    use cs_buffer::{ProverBuffer, VerifierBuffer};
    use curve25519_dalek::ristretto::CompressedRistretto;
    use gadget::Gadget;

    #[test]
    fn test_or_conjunction_1() {
        // HASH GADGET: 1946 Constraints

        let preimage_1: Vec<u8> = vec![
            0x38, 0x53, 0x54, 0x50, 0x43, 0x30, 0x43, 0x54, 
            0x6f, 0x31, 0x38, 0x77, 0x61, 0x5a, 0x6a, 0x42, 
            0x36, 0x63
        ];

        let image_1: Scalar = be_to_scalar(&vec![
            0x0d, 0x22, 0x03, 0x06, 0x9a, 0xc1, 0x5f, 0x58, 
            0x17, 0x2b, 0xae, 0x1b, 0x3a, 0xf9, 0x8d, 0x89, 
            0x82, 0xde, 0xef, 0x9d, 0xf3, 0x74, 0x82, 0xc1, 
            0xa9, 0x20, 0xb8, 0x83, 0x2e, 0xe8, 0x13, 0xa4
        ]);
        
        let preimage_2: Vec<u8> = vec![
            0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x4a, 
            0x76, 0x07, 0x7d, 0x4a, 0x40, 0xbd, 0x91, 0x55, 
            0x1b, 0x3a, 0x03, 0xb1, 0xad, 0x8a, 0xdb, 0x2b, 
            0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70, 
            0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70, 
            0x73, 0x20, 0x6f, 0x76, 0x65
        ];

        let image_2: Scalar = be_to_scalar(&vec![
            0x0f, 0xcb, 0x21, 0xfb, 0xf2, 0x3b, 0x96, 0x8d, 
            0xee, 0x8f, 0x6b, 0x3a, 0x51, 0x1e, 0x93, 0xe8, 
            0xc5, 0xc0, 0xeb, 0x2f, 0x71, 0xaa, 0x06, 0x01, 
            0x11, 0x1f, 0x91, 0x1c, 0x9e, 0x42, 0xcf, 0x06
        ]);

        let preimage_3: Vec<u8> = vec![
            0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x63, 
            0x6b, 0x20, 0x62, 0x72, 0x6f, 0x77, 0x6e, 0x20, 
            0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70, 
            0x73, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x20, 0x74
        ];

        let image_3: Scalar = be_to_scalar(&vec![
            0x01, 0x24, 0x54, 0x09, 0xf2, 0x8a, 0xe2, 0xf0, 
            0x76, 0x07, 0x7d, 0x4a, 0x40, 0xbd, 0x91, 0x55, 
            0x1b, 0x3a, 0x03, 0xb1, 0xad, 0x8a, 0xdb, 0x2b, 
            0x1d, 0xa1, 0x16, 0xd2, 0x9c, 0x60, 0xa8, 0x5c
        ]);

        let bp_gens = BulletproofGens::new(8192, 1);

        let pc_gens = PedersenGens::default();
        let mut main_transcript = Transcript::new(b"MiMCHash");
        let mut prover_main = Prover::new(&pc_gens, &mut main_transcript);

        let or_gens = PedersenGens::default();
        let mut or_transcript = Transcript::new(b"OrTranscript");
        let or_prover = Prover::new(&or_gens, &mut or_transcript);
        let mut prover_buffer = ProverBuffer::new(or_prover);

        // First OR Clause
        let (wtns_coms_1, drvd_coms_1) = mimc_hash_prover(&mut prover_main, &mut prover_buffer, image_1, &preimage_1);
        prover_buffer.rewind();

        // Second OR Clause
        let (wtns_coms_2, drvd_coms_2) = mimc_hash_prover(&mut prover_main, &mut prover_buffer, image_2, &preimage_2);
        prover_buffer.rewind();

        // Third OR Clause
        let (wtns_coms_3, drvd_coms_3) = mimc_hash_prover(&mut prover_main, &mut prover_buffer, image_3, &preimage_3);
        prover_buffer.rewind();
        
        or(&mut prover_main, &prover_buffer);

        // Genereate Proof
        let proof = prover_main.prove(&bp_gens).unwrap();

        // Verifier
        let mut verifier_transcript = Transcript::new(b"MiMCHash");
        let mut verifier_main = Verifier::new(&mut verifier_transcript);

        let mut or_transcript = Transcript::new(b"OrTranscript");
        let or_verifier = Verifier::new(&mut or_transcript);
        let mut verifier_buffer = VerifierBuffer::new(or_verifier);

        // First OR Clause
        let witness_vars_1: Vec<Variable> = verifier_commit(&mut verifier_main, wtns_coms_1);
        let derived_vars_1: Vec<Variable> = verifier_commit(&mut verifier_main, drvd_coms_1);
        
        mimc_hash_verifier(&mut verifier_buffer, image_1, &witness_vars_1, &derived_vars_1);
        verifier_buffer.rewind();

        // Second OR Clause
        let witness_vars_2: Vec<Variable> = verifier_commit(&mut verifier_main, wtns_coms_2);
        let derived_vars_2: Vec<Variable> = verifier_commit(&mut verifier_main, drvd_coms_2);

        mimc_hash_verifier(&mut verifier_buffer, image_2, &witness_vars_2, &derived_vars_2);
        verifier_buffer.rewind();

        // Third OR Clause
        let witness_vars_3: Vec<Variable> = verifier_commit(&mut verifier_main, wtns_coms_3);
        let derived_vars_3: Vec<Variable> = verifier_commit(&mut verifier_main, drvd_coms_3);
        
        mimc_hash_verifier(&mut verifier_buffer, image_3, &witness_vars_3, &derived_vars_3);
        verifier_buffer.rewind();

        or(&mut verifier_main, &verifier_buffer);

        assert!(verifier_main.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    fn mimc_hash_prover(
        prover_main: &mut Prover,
        prover_buffer: &mut ProverBuffer,
        image: Scalar,
        preimage: &Vec<u8>
    ) -> (Vec<CompressedRistretto>, Vec<CompressedRistretto>) {
        let (witness_scalars, witness_commitments, variables) = commit(prover_main, preimage);
        prover_buffer.commit(&witness_scalars);

        let gadget = MimcHash256::new(image.into());
        let (derived_commitments, derived_witnesses) = gadget.setup(prover_main, &witness_scalars);

        prover_buffer.commit(&derived_witnesses.clone().into_iter().map(|derived| derived.0.unwrap()).collect());
    
        gadget.prove(prover_buffer, &variables, &derived_witnesses);

        (witness_commitments, derived_commitments)
    }

    fn mimc_hash_verifier(
        verifier_buffer: &mut VerifierBuffer,
        image: Scalar,
        witness_vars: &Vec<Variable>,
        derived_vars: &Vec<Variable>
    ) {
        let gadget = MimcHash256::new(image.into());

        gadget.verify(verifier_buffer, witness_vars, derived_vars);
    }
}