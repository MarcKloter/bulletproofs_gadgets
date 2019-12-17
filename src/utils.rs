use bulletproofs::r1cs::{ConstraintSystem, LinearCombination};
use curve25519_dalek::scalar::Scalar;

/// Enforces that the quantity of x is in the range [0, 2^n).
pub fn range_proof(
    cs: &mut dyn ConstraintSystem,
    mut x: LinearCombination,
    n: u8,
    x_assignment: Option<Scalar>
) {
    let mut exp_2 = Scalar::one();
    let x_bytes: Option<&[u8; 32]> = x_assignment.as_ref().map(|scalar| scalar.as_bytes());
    for i in 0..n {
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

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use conversions::{be_to_scalar};
    use bulletproofs::r1cs::{Prover, Verifier};

    #[test]
    fn test_range_proof_1() {
        let x_assignment: Scalar = be_to_scalar(&vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e
        ]);

        let x: LinearCombination = x_assignment.into();

        let n = 56;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(256, 1);

        let mut prover_transcript = Transcript::new(b"RangeProof");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
        range_proof(&mut prover, x.clone(), n, Some(x_assignment));
        let proof = prover.prove(&bp_gens).unwrap();
        
        let mut verifier_transcript = Transcript::new(b"RangeProof");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        range_proof(&mut verifier, x.clone(), n, None);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
    #[test]
    fn test_range_proof_2() {
        let x_assignment: Scalar = be_to_scalar(&vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e
        ]);

        let x: LinearCombination = x_assignment.into();

        let n = 48;

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(256, 1);

        let mut prover_transcript = Transcript::new(b"RangeProof");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
        range_proof(&mut prover, x.clone(), n, Some(x_assignment));
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"RangeProof");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        range_proof(&mut verifier, x.clone(), n, None);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }
}
