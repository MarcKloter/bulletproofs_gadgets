use bulletproofs::r1cs::{ConstraintSystem, Variable, Prover};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use rand::thread_rng;

pub trait Gadget {
    /// Preprocess witnesses to derive optional gadget-specific commitments 
    fn preprocess(&self, witnesses: &Vec<Scalar>) -> Vec<Scalar>;

    /// Build the constraint system
    fn assemble(
        &self, 
        cs: &mut dyn ConstraintSystem, 
        witnesses: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    );
    
    fn setup(
        &self, 
        prover: &mut Prover, 
        witnesses: &Vec<Scalar>
    ) -> (Vec<CompressedRistretto>, Vec<(Option<Scalar>, Variable)>) {
        let derived_scalars: Vec<Scalar> = self.preprocess(witnesses);

        // create gadget-specific pedersen commitments
        let mut commitments: Vec<CompressedRistretto> = Vec::new(); 
        let derived_witnesses: Vec<(Option<Scalar>, Variable)> = derived_scalars
            .iter()
            .cloned()
            .map(|scalar| {
                let (com, var) = prover.commit(scalar, Scalar::random(&mut thread_rng()));
                commitments.push(com);
                (Some(scalar), var)
            })
            .collect();

        (commitments, derived_witnesses)
    }

    fn prove(
        &self, 
        prover: &mut dyn ConstraintSystem, 
        commitment_vars: &Vec<Variable>,
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) {
        self.assemble(prover, &commitment_vars, &derived_witnesses);
    }

    fn verify(
        &self, 
        verifier: &mut dyn ConstraintSystem, 
        witnesses: &Vec<Variable>, 
        derived: &Vec<Variable>
    ) {
        let derived_witnesses = derived.iter().cloned().map(|com| (None, com)).collect();

        self.assemble(verifier, &witnesses, &derived_witnesses);
    }
}
