use bulletproofs::r1cs::{ConstraintSystem, Variable, LinearCombination};
use curve25519_dalek::scalar::Scalar;
use gadget::Gadget;
use conversions::be_to_scalar;
use utils::range_proof;

pub struct BoundsCheck {
    min: Scalar,
    max: Scalar,
    n: u8
}

impl Gadget for BoundsCheck {
    fn preprocess(&self, witnesses: &Vec<Scalar>) -> Vec<Scalar> {
        let mut derived_witnesses: Vec<Scalar> = Vec::new();
        let v: Scalar = witnesses[0];
        derived_witnesses.push(v - self.min);
        derived_witnesses.push(self.max - v);

        derived_witnesses
    }

    fn assemble(
        &self, 
        cs: &mut dyn ConstraintSystem, 
        _: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) {
        let (a_assignment, a) = derived_witnesses[0];
        let (b_assignment, b) = derived_witnesses[1];
        // a = v - min
        let a_lc: LinearCombination = a.into();
        // b = max - v
        let b_lc: LinearCombination = b.into();

        let a_plus_b: LinearCombination = a_lc.clone() + b_lc.clone();
        let max_minus_min: LinearCombination = (self.max - self.min).into();

        // constrain: (a + b) - (max - min) = 0
        cs.constrain(a_plus_b - max_minus_min);

        // Constrain a in [0, 2^n)
        range_proof(cs, a_lc, self.n, a_assignment);

        // Constrain b in [0, 2^n)
        range_proof(cs, b_lc, self.n, b_assignment);
    }
}

impl BoundsCheck {
    /// # Arguments
    /// * `min` - u64 as byte vector in big endian order 
    /// * `max` - u64 as byte vector in big endian order 
    pub fn new(min: &Vec<u8>, max: &Vec<u8>) -> BoundsCheck {
        // number of bits to represent max
        let n: u8 = (max.len() * 8) as u8;

        BoundsCheck {
            min: be_to_scalar(min),
            max: be_to_scalar(max),
            n: n
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use commitments::{commit, verifier_commit};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;
    use bulletproofs::r1cs::{Prover, Verifier};

    #[test]
    fn test_bounds_check_gadget() {
        let min: Vec<u8> = vec![10];
        let max: Vec<u8> = vec![100];
        let witness: Vec<u8> = vec![67];

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(16, 1);

        let mut prover_transcript = Transcript::new(b"BoundsCheck");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = BoundsCheck::new(&min, &max);
        let (scalars, witness_commitments, variables) = commit(&mut prover, &witness);
        let (derived_commitments, derived_witnesses) = gadget.setup(&mut prover, &scalars);
        gadget.prove(&mut prover, &variables, &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"BoundsCheck");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}