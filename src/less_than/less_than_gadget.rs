use bulletproofs::r1cs::{ConstraintSystem, Variable, LinearCombination};
use curve25519_dalek::scalar::Scalar;
use gadget::Gadget;
use utils::range_proof;

/// Gadget proving that LEFT < RIGHT (witness and instance variables allowed)
/// LEFT and RIGHT are limited to 126 bits --> range: [0, 2^126)
pub struct LessThan {
    left_hand: LinearCombination,
    left_hand_assignment: Option<Scalar>,
    right_hand: LinearCombination,
    right_hand_assignment: Option<Scalar>
}

impl Gadget for LessThan {
    fn preprocess(&self, _: &Vec<Scalar>) -> Vec<Scalar> {
        assert!(self.left_hand_assignment.is_some(), "missing right hand assignment");
        assert!(self.right_hand_assignment.is_some(), "missing right hand assignment");
        let left: Scalar = self.left_hand_assignment.unwrap();
        let right: Scalar = self.right_hand_assignment.unwrap();

        let mut derived_witnesses: Vec<Scalar> = Vec::new();
        let delta: Scalar = right - left;

        derived_witnesses.push(delta);

        if delta == Scalar::zero() {
            derived_witnesses.push(Scalar::zero());
        } else {
            let delta_inv: Scalar = delta.invert();
            derived_witnesses.push(delta_inv);
        }

        derived_witnesses
    }

    fn assemble(
        &self, 
        cs: &mut dyn ConstraintSystem, 
        _: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) {
        // retrieve delta from derived witnesses
        let (delta_assignment, delta): (Option<Scalar>, Variable) = *derived_witnesses.get(0).unwrap();
        let delta_lc: LinearCombination = LinearCombination::from(delta);

        // retrieve inverse of delta from derived witnesses
        let (_, delta_inv): (Option<Scalar>, Variable) = *derived_witnesses.get(1).unwrap();
        let delta_inv_lc: LinearCombination = LinearCombination::from(delta_inv);

        // show that left, right and delta are all within [0, 2^126)
        let n = 126;
        range_proof(cs, self.left_hand.clone(), n, self.left_hand_assignment);
        range_proof(cs, self.right_hand.clone(), n, self.right_hand_assignment);
        range_proof(cs, delta_lc.clone(), n, delta_assignment);

        // show that delta * delta_inv = 1 --> delta != 0 (and thus left != right)
        let one_lc: LinearCombination = LinearCombination::from(Scalar::one());
        let (_, _, should_be_one) = cs.multiply(delta_lc.clone(), delta_inv_lc);
        cs.constrain(one_lc - should_be_one);

        let right_minus_left = self.right_hand.clone() - self.left_hand.clone();

        // show that right - left - delta = 0
        cs.constrain(right_minus_left - delta_lc);
    }
}

impl LessThan {
    pub fn new(
        left_hand: LinearCombination, 
        left_hand_assignment: Option<Scalar>,
        right_hand: LinearCombination, 
        right_hand_assignment: Option<Scalar>
    ) -> LessThan {
        LessThan {
            left_hand: left_hand,
            left_hand_assignment: left_hand_assignment,
            right_hand: right_hand,
            right_hand_assignment: right_hand_assignment
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use commitments::verifier_commit;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;
    use bulletproofs::r1cs::{Prover, Verifier};
    use conversions::be_to_scalar;

    /// generic happy case
    #[test]
    fn test_less_than_gadget_1() {
        let right: Vec<u8> = vec![
            0xaa, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc
        ];

        let right_assignment: Scalar = be_to_scalar(&right);

        let right_lc: LinearCombination = right_assignment.into();
            
        let left: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc
        ];

        let left_assignment: Scalar = be_to_scalar(&left);

        let left_lc: LinearCombination = left_assignment.into();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(1024, 1);

        let mut prover_transcript = Transcript::new(b"LessThan");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = LessThan::new(left_lc, Some(left_assignment), right_lc, Some(right_assignment));
        let (derived_commitments, derived_witnesses) = gadget.setup(&mut prover, &Vec::new());
        gadget.prove(&mut prover, &Vec::new(), &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"LessThan");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &Vec::new(), &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    /// swap of generic happy case
    #[test]
    fn test_less_than_gadget_2() {
        let right: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc
        ];

        let right_assignment: Scalar = be_to_scalar(&right);

        let right_lc: LinearCombination = right_assignment.into();
            
        let left: Vec<u8> = vec![
            0xaa, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc
        ];

        let left_assignment: Scalar = be_to_scalar(&left);

        let left_lc: LinearCombination = left_assignment.into();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(1024, 1);

        let mut prover_transcript = Transcript::new(b"LessThan");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = LessThan::new(left_lc, Some(left_assignment), right_lc, Some(right_assignment));
        let (derived_commitments, derived_witnesses) = gadget.setup(&mut prover, &Vec::new());
        gadget.prove(&mut prover, &Vec::new(), &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"LessThan");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &Vec::new(), &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    /// set left and right to maximum allowed values
    #[test]
    fn test_less_than_gadget_3() {
        // 2^126 - 1
        let right: Vec<u8> = vec![
            0x3f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
        ];

        let right_assignment: Scalar = be_to_scalar(&right);

        let right_lc: LinearCombination = right_assignment.into();
            
        // 2^126 - 2
        let left: Vec<u8> = vec![
            0x3f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe
        ];

        let left_assignment: Scalar = be_to_scalar(&left);

        let left_lc: LinearCombination = left_assignment.into();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(1024, 1);

        let mut prover_transcript = Transcript::new(b"LessThan");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = LessThan::new(left_lc, Some(left_assignment), right_lc, Some(right_assignment));
        let (derived_commitments, derived_witnesses) = gadget.setup(&mut prover, &Vec::new());
        gadget.prove(&mut prover, &Vec::new(), &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"LessThan");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &Vec::new(), &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    /// swap of maximum value test
    #[test]
    fn test_less_than_gadget_4() {
        // 2^126 - 2
        let right: Vec<u8> = vec![
            0x3f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe
        ];

        let right_assignment: Scalar = be_to_scalar(&right);

        let right_lc: LinearCombination = right_assignment.into();
            
        // 2^126 - 1
        let left: Vec<u8> = vec![
            0x3f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
        ];

        let left_assignment: Scalar = be_to_scalar(&left);

        let left_lc: LinearCombination = left_assignment.into();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(1024, 1);

        let mut prover_transcript = Transcript::new(b"LessThan");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = LessThan::new(left_lc, Some(left_assignment), right_lc, Some(right_assignment));
        let (derived_commitments, derived_witnesses) = gadget.setup(&mut prover, &Vec::new());
        gadget.prove(&mut prover, &Vec::new(), &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"LessThan");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &Vec::new(), &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    /// left and right equal: zero
    #[test]
    fn test_less_than_gadget_5() {
        let right: Vec<u8> = vec![
            0x00
        ];

        let right_assignment: Scalar = be_to_scalar(&right);

        let right_lc: LinearCombination = right_assignment.into();
            
        let left: Vec<u8> = vec![
            0x00
        ];

        let left_assignment: Scalar = be_to_scalar(&left);

        let left_lc: LinearCombination = left_assignment.into();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(1024, 1);

        let mut prover_transcript = Transcript::new(b"LessThan");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = LessThan::new(left_lc, Some(left_assignment), right_lc, Some(right_assignment));
        let (derived_commitments, derived_witnesses) = gadget.setup(&mut prover, &Vec::new());
        gadget.prove(&mut prover, &Vec::new(), &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"LessThan");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &Vec::new(), &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    /// left and right equal: 2^126 - 1
    #[test]
    fn test_less_than_gadget_6() {
        let right: Vec<u8> = vec![
            0x3f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
        ];

        let right_assignment: Scalar = be_to_scalar(&right);

        let right_lc: LinearCombination = right_assignment.into();
            
        let left: Vec<u8> = vec![
            0x3f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
        ];

        let left_assignment: Scalar = be_to_scalar(&left);

        let left_lc: LinearCombination = left_assignment.into();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(1024, 1);

        let mut prover_transcript = Transcript::new(b"LessThan");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = LessThan::new(left_lc, Some(left_assignment), right_lc, Some(right_assignment));
        let (derived_commitments, derived_witnesses) = gadget.setup(&mut prover, &Vec::new());
        gadget.prove(&mut prover, &Vec::new(), &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"LessThan");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &Vec::new(), &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }
}