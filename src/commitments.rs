use bulletproofs::r1cs::{Variable, Prover, Verifier};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use conversions::{be_to_scalar, be_to_scalars};
use rand::thread_rng;

/// Commit to multiple witnesses of 32 or less bytes each
pub fn commit_all_single(prover: &mut Prover, witnesses: &Vec<Vec<u8>>) -> (Vec<Scalar>, Vec<CompressedRistretto>, Vec<Variable>) {
    let (mut scalars, mut commitments, mut variables) = (Vec::new(), Vec::new(), Vec::new());

    for witness in witnesses {
        let (scalar, commitment, variable) = commit_single(prover, &witness);
        scalars.push(scalar);
        commitments.push(commitment);
        variables.push(variable);
    }
    
    (scalars, commitments, variables)
}

/// Commit to a witness of 32 or less bytes
pub fn commit_single(prover: &mut Prover, witness: &Vec<u8>) -> (Scalar, CompressedRistretto, Variable) {
    assert!(witness.len() <= 32, "the provided witness is longer than 32 bytes");
    
    let scalar: Scalar = be_to_scalar(&witness);

    let (commitment, variable) = prover.commit(scalar, Scalar::random(&mut thread_rng()));

    (scalar, commitment, variable)
}

/// Commit to a variable length witness
/// If the given witness is longer than 32 bytes, it will be split up into multiple commitments
pub fn commit(prover: &mut Prover, witness: &Vec<u8>) -> (Vec<Scalar>, Vec<CompressedRistretto>, Vec<Variable>) {
    let scalars: Vec<Scalar> = be_to_scalars(&witness);

    let (commitments, variables) = scalars
        .iter()
        .map(|scalar| prover.commit(*scalar, Scalar::random(&mut thread_rng())))
        .unzip();

    (scalars, commitments, variables)
}

pub fn verifier_commit(verifier: &mut Verifier, commitments: Vec<CompressedRistretto>) -> Vec<Variable> {
    commitments.iter().map(|commitment| verifier.commit(*commitment)).collect()
}