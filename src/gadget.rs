use bulletproofs::r1cs::{ConstraintSystem, Variable, Prover, Verifier};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand::thread_rng;

pub trait Gadget {
    /// Constructor
    fn new(instance_vars: &Vec<Vec<u8>>) -> Self;

    /// Encode witness variables Vec<Vec<u8>> as Vec<Scalar> to commit to
    fn preprocess(&self, witness_vars: &Vec<Vec<u8>>) -> Vec<Scalar>;

    /// Build the constraint system
    fn assemble(&self, cs: &mut ConstraintSystem, commitment_variables: &Vec<Variable>);

    fn prove(&self, prover: &mut Prover, witness_vars: &Vec<Vec<u8>>) -> Vec<CompressedRistretto> {
        let witness_vars = self.preprocess(witness_vars);

        // create pedersen commitments for witness variables
        let (commitments, vars) = witness_vars
            .iter()
            .map(|w| prover.commit(*w, Scalar::random(&mut thread_rng())))
            .unzip();

        self.assemble(prover, &vars);

        commitments
    }

    fn verify(&self, verifier: &mut Verifier, commitments: &Vec<CompressedRistretto>) {
        // get variables from prover commitments
        let vars = commitments
            .iter()
            .map(|commitment| verifier.commit(*commitment))
            .collect();

        self.assemble(verifier, &vars);
    }
}
