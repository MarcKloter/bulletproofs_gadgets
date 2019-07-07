use bulletproofs::r1cs::{ConstraintSystem, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use gadget::Gadget;

struct Bounds {
    min: u64,
    max: u64
}

struct BoundsCheck {
    min: Scalar,
    max: Scalar,
    n: u8
}

impl Gadget<Bounds, u64> for BoundsCheck {
    fn new(instance_vars: &Bounds) -> BoundsCheck {
        // number of bits to represent max = floor(log2(max) + 1)
        let n: u8 = ((instance_vars.max as f64).log2() + 1.0).floor() as u8;

        BoundsCheck {
            min: instance_vars.min.into(),
            max: instance_vars.max.into(),
            n: n
        }
    }

    /// Encode witness variable as Vec<Scalar>, {0: v, 1: a, 2: b}
    fn preprocess(&self, witness: &u64) -> Vec<Scalar> {
        let mut witness_scalar: Vec<Scalar> = Vec::new();

        witness_scalar.push((*witness).into());

        let v: Scalar = witness_scalar[0];
        witness_scalar.push(v - self.min);
        witness_scalar.push(self.max - v);

        witness_scalar
    }

    fn assemble(&self, cs: &mut ConstraintSystem, commitments: &Vec<Variable>, witnesses: Option<Vec<Scalar>>) {
        // a = v - min
        let a_lc: LinearCombination = commitments[1].into();
        // b = max - v
        let b_lc: LinearCombination = commitments[2].into();

        let a_plus_b: LinearCombination = a_lc.clone() + b_lc.clone();
        let max_minus_min: LinearCombination = (self.max - self.min).into();

        // constrain: (a + b) - (max - min) = 0
        cs.constrain(a_plus_b - max_minus_min);

        // Constrain a in [0, 2^n)
        self.range_proof(cs, a_lc, witnesses.clone().map(|vec| vec[1]));

        // Constrain b in [0, 2^n)
        self.range_proof(cs, b_lc, witnesses.clone().map(|vec| vec[2]));
    }
}

impl BoundsCheck {
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

    #[test]
    fn test_mimc_hash_gadget() {
        let min: u64 = 10;
        let max: u64 = 100;

        let v: u64 = 67;
        
        let instance_vars: Bounds = Bounds { min: min, max: max };
        let witness_vars: u64 = v;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let mut prover_transcript = Transcript::new(b"BoundsCheck");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = BoundsCheck::new(&instance_vars);
        let commitments = gadget.prove(&mut prover, &witness_vars);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"BoundsCheck");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        
        gadget.verify(&mut verifier, &commitments);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}