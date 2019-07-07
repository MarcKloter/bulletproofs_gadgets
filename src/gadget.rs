use bulletproofs::r1cs::{ConstraintSystem, Variable, Prover, Verifier};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand::thread_rng;

/// Gadget with instance variable type T and witness variable type U
pub trait Gadget<T, U> {
    /// Constructor
    fn new(instance_vars: &T) -> Self;

    /// Encode witnesses as Vec<Scalar> to commit to
    fn preprocess(&self, witnesses: &U) -> Vec<Scalar>;

    /// Build the constraint system
    fn assemble(&self, cs: &mut ConstraintSystem, commitments: &Vec<Variable>, witnesses: Option<Vec<Scalar>>);

    fn prove(&self, prover: &mut Prover, witnesses: &U) -> Vec<CompressedRistretto> {
        let witness_scalars: Vec<Scalar> = self.preprocess(witnesses);

        // create pedersen commitments for witness variables
        let (commitments, vars) = witness_scalars
            .iter()
            .map(|w| prover.commit(*w, Scalar::random(&mut thread_rng())))
            .unzip();

        self.assemble(prover, &vars, Some(witness_scalars));

        commitments
    }

    fn verify(&self, verifier: &mut Verifier, commitments: &Vec<CompressedRistretto>) {
        // get variables from prover commitments
        let vars = commitments
            .iter()
            .map(|commitment| verifier.commit(*commitment))
            .collect();

        self.assemble(verifier, &vars, None);
    }
}
