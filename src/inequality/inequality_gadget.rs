use bulletproofs::r1cs::{ConstraintSystem, Variable, LinearCombination};
use curve25519_dalek::scalar::Scalar;
use gadget::Gadget;

// Gadget proving inequality LEFT < RIGHT or LEFT > RIGHT, where LEFT is a witness and RIGHT can be either a witness or instance variable
pub struct Inequality {
    right_hand: Vec<LinearCombination>,
    right_hand_assignment: Option<Vec<Scalar>>
}

impl Gadget for Inequality {
    fn preprocess(&self, left_hand: &Vec<Scalar>) -> Vec<Scalar> {
        assert!(self.right_hand_assignment.is_some(), "missing right hand assignment");
        let right_hand: &Vec<Scalar> = self.right_hand_assignment.as_ref().unwrap();

        let mut derived_witnesses: Vec<Scalar> = Vec::new();

        let mut sum: Scalar = Scalar::zero();

        for i in 0..left_hand.len() {
            let left: Scalar = *left_hand.get(i).unwrap();
            let right: Scalar = *right_hand.get(i).unwrap_or(&Scalar::zero());
            // delta has to be max(left, right) - min(left, right)
            let delta: Scalar;
            if Inequality::compare(left, right) {
                // case: left >= right
                delta = left - right;
            } else {
                // case: left < right
                delta = right - left;
            }
            derived_witnesses.push(delta);
            if delta == Scalar::zero() {
                derived_witnesses.push(Scalar::zero());
            } else {
                let delta_inv: Scalar = delta.invert();
                derived_witnesses.push(delta_inv);
                sum = sum + (delta * delta_inv);
            }
        }
        
        derived_witnesses.push(sum.invert());

        derived_witnesses
    }

    fn assemble(
        &self, 
        cs: &mut dyn ConstraintSystem, 
        left_hand: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) {
        if self.right_hand.len() != left_hand.len() {
            return cs.constrain(Scalar::one().into());
        }

        // sum up all deltas, if left = right then this would be 0 (as all deltas would be 0)
        // showing that there is a multiplicative inverse to this sum proves, that there is at least one delta != 0 --> left != right
        let mut sum: LinearCombination = LinearCombination::from(Scalar::zero());

        for i in 0..left_hand.len() {
            let right_lc : LinearCombination = self.right_hand.get(i).unwrap().clone();
            let left_lc : LinearCombination = LinearCombination::from(*left_hand.get(i).unwrap());
            let (_, delta): (Option<Scalar>, Variable) = *derived_witnesses.get(i*2).unwrap();
            let delta_lc: LinearCombination = LinearCombination::from(delta);
            let (_, delta_inv): (Option<Scalar>, Variable) = *derived_witnesses.get(i*2+1).unwrap();
            let delta_inv_lc = LinearCombination::from(delta_inv);

            // show that (left - right - delta) = 0 or (right - left - delta) = 0 
            let left_minus_right = left_lc.clone() - right_lc.clone();
            let right_minus_left = right_lc.clone() - left_lc.clone();
            let left = left_minus_right - delta;
            let right = right_minus_left - delta;
            let (_, _, should_be_zero) = cs.multiply(left, right);
            cs.constrain(should_be_zero.into());

            // multiply delta * delta_inv, if delta is non-zero this will be 1, otherwise 0
            let (_, _, zero_or_one) = cs.multiply(delta_lc, delta_inv_lc);

            sum = sum + zero_or_one;
        }

        let sum_inv: LinearCombination = LinearCombination::from((*derived_witnesses.get(derived_witnesses.len() - 1).unwrap()).1);

        let (_, _, should_be_one) = cs.multiply(sum, sum_inv);
        let should_be_one_lc: LinearCombination = LinearCombination::from(should_be_one);

        let one_lc: LinearCombination = LinearCombination::from(Scalar::one());

        // show that sum * sum_inv = 1
        cs.constrain(one_lc - should_be_one_lc);
    }
}

impl Inequality {
    pub fn new(right_hand: Vec<LinearCombination>, right_hand_assignment: Option<Vec<Scalar>>) -> Inequality {
        Inequality {
            right_hand: right_hand,
            right_hand_assignment: right_hand_assignment
        }
    }

    pub fn compare(left: Scalar, right: Scalar) -> bool {
        for i in (0..32).rev() {
            if left.as_bytes().get(i).unwrap() > right.as_bytes().get(i).unwrap() {
                return true
            } else if left.as_bytes().get(i).unwrap() < right.as_bytes().get(i).unwrap() {
                return false
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use commitments::{commit, verifier_commit};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use merlin::Transcript;
    use bulletproofs::r1cs::{Prover, Verifier};
    use conversions::be_to_scalars;

    #[test]
    fn test_inequality_gadget_1() {
        let right: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x73, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49,
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x02, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49,
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8c, 0xeb, 0x66, 0x87, 0x49
        ];

        let right_assignment: Vec<Scalar> = be_to_scalars(&right);

        let right_lc: Vec<LinearCombination> = right_assignment
            .iter()
            .map(|scalar| (*scalar).into())
            .collect();
            
        let left_assignment: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49,
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49,
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8c, 0xeb, 0x66, 0x87, 0x49
        ];

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(8, 1);

        let mut prover_transcript = Transcript::new(b"Inequality");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = Inequality::new(right_lc, Some(right_assignment));
        let (scalars, witness_commitments, variables) = commit(&mut prover, &left_assignment);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"Inequality");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_inequality_gadget_2() {
        let right: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x73, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49
        ];

        let right_assignment: Vec<Scalar> = be_to_scalars(&right);

        let right_lc: Vec<LinearCombination> = right_assignment
            .iter()
            .map(|scalar| (*scalar).into())
            .collect();
            
        let left_assignment: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49
        ];

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(4, 1);

        let mut prover_transcript = Transcript::new(b"Inequality");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = Inequality::new(right_lc, Some(right_assignment));
        let (scalars, witness_commitments, variables) = commit(&mut prover, &left_assignment);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"Inequality");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_inequality_gadget_3() {
        // case: right > left
        
        let right: Vec<u8> = vec![
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
        ];

        let right_assignment: Vec<Scalar> = be_to_scalars(&right);

        let right_lc: Vec<LinearCombination> = right_assignment
            .iter()
            .map(|scalar| (*scalar).into())
            .collect();
            
        let left_assignment: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87
        ];

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(4, 1);

        let mut prover_transcript = Transcript::new(b"Inequality");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = Inequality::new(right_lc, Some(right_assignment));
        let (scalars, witness_commitments, variables) = commit(&mut prover, &left_assignment);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"Inequality");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_inequality_gadget_4() {
        let right: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87
        ];

        let right_assignment: Vec<Scalar> = be_to_scalars(&right);

        let right_lc: Vec<LinearCombination> = right_assignment
            .iter()
            .map(|scalar| (*scalar).into())
            .collect();
            
        let left_assignment: Vec<u8> = vec![
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
        ];

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(4, 1);

        let mut prover_transcript = Transcript::new(b"Inequality");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = Inequality::new(right_lc, Some(right_assignment));
        let (scalars, witness_commitments, variables) = commit(&mut prover, &left_assignment);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"Inequality");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_inequality_gadget_5() {
        let value: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x73, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49
        ];

        let right_assignment: Vec<Scalar> = be_to_scalars(&value);

        let right_lc: Vec<LinearCombination> = right_assignment
            .iter()
            .map(|scalar| (*scalar).into())
            .collect();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(4, 1);

        let mut prover_transcript = Transcript::new(b"Inequality");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = Inequality::new(right_lc, Some(right_assignment));
        let (scalars, witness_commitments, variables) = commit(&mut prover, &value);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"Inequality");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    #[test]
    fn test_inequality_gadget_6() {
        let right: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87
        ];

        let right_assignment: Vec<Scalar> = be_to_scalars(&right);

        let right_lc: Vec<LinearCombination> = right_assignment
            .iter()
            .map(|scalar| (*scalar).into())
            .collect();
            
        let left_assignment: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79,
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e 
        ];

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(4, 1);

        let mut prover_transcript = Transcript::new(b"Inequality");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = Inequality::new(right_lc, Some(right_assignment));
        let (scalars, witness_commitments, variables) = commit(&mut prover, &left_assignment);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"Inequality");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    #[test]
    fn test_inequality_gadget_7() {
        let right: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79,
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e 
        ];

        let right_assignment: Vec<Scalar> = be_to_scalars(&right);

        let right_lc: Vec<LinearCombination> = right_assignment
            .iter()
            .map(|scalar| (*scalar).into())
            .collect();
            
        let left_assignment: Vec<u8> = vec![
            0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
            0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
            0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
            0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87
        ];

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(4, 1);

        let mut prover_transcript = Transcript::new(b"Inequality");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = Inequality::new(right_lc, Some(right_assignment));
        let (scalars, witness_commitments, variables) = commit(&mut prover, &left_assignment);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"Inequality");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }
}