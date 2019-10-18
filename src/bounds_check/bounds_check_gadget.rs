use bulletproofs::r1cs::{ConstraintSystem, Variable, LinearCombination};
use curve25519_dalek::scalar::Scalar;
use gadget::Gadget;
use conversions::be_to_scalar;

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
        cs: &mut ConstraintSystem, 
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
        self.range_proof(cs, a_lc, a_assignment);

        // Constrain b in [0, 2^n)
        self.range_proof(cs, b_lc, b_assignment);
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

    /// Enforces that the quantity of x is in the range [0, 2^n).
    fn range_proof(
        &self,
        cs: &mut ConstraintSystem,
        mut x: LinearCombination,
        x_assignment: Option<Scalar>
    ) {
        let mut exp_2 = Scalar::one();
        let x_bytes: Option<&[u8; 32]> = x_assignment.as_ref().map(|scalar| scalar.as_bytes());
        for i in 0..self.n {
            // Create low-level variables and add them to constraints
            let (a, b, o) = cs.allocate_multiplier(x_bytes.map(|byte_arr| {
                let offset: u8 = i/8;
                let bit: u8 = (byte_arr[offset as usize] >> (i - offset*8)) & 1u8;
                ((1 - bit).into(), bit.into())
            })).unwrap();

            // Enforce a * b = 0, so one of (a,b) is zero
            cs.constrain(o.into());

            // Enforce that a = 1 - b, so they both are 1 or 0.
            cs.constrain(a + (b - 1u8));

            // Add -b_i*2^i to the linear combination, so after the loop we have x = Sum(b_i * 2^i, i = 0..n-1)
            x = x - b * exp_2;

            exp_2 = exp_2 + exp_2;
        }

        // Enforce that x = Sum(b_i * 2^i, i = 0..n-1)
        cs.constrain(x);
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
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"BoundsCheck");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}