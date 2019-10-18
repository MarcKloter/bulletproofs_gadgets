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
        assert!(right_hand.len() == left_hand.len(), "left and right hand side are not the same length");

        let mut derived_witnesses: Vec<Scalar> = Vec::new();

        let mut sum: Scalar = Scalar::zero();

        for i in 0..right_hand.len() {
            let delta: Scalar = left_hand.get(i).unwrap() - right_hand.get(i).unwrap();
            let delta_inv: Scalar = delta.invert();
            derived_witnesses.push(delta);
            derived_witnesses.push(delta_inv);
            sum = sum + delta * delta_inv;
        }

        derived_witnesses.push(sum.invert());

        derived_witnesses
    }

    fn assemble(
        &self, 
        cs: &mut ConstraintSystem, 
        left_hand: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) {
        assert!(self.right_hand.len() == left_hand.len(), "left and right hand side are not the same length");

        // sum up all deltas, if left = right then this would be 0 (as all deltas would be 0)
        // showing that there is a multiplicative inverse to this sum proves, that there is at least one delta != 0 --> left != right
        let mut sum: LinearCombination = LinearCombination::from(Scalar::zero());

        for i in 0..left_hand.len() {
            let right_lc : LinearCombination = self.right_hand.get(i).unwrap().clone();
            let left_lc : LinearCombination = (*left_hand.get(i).unwrap()).into();
            let (_, delta) = derived_witnesses.get(i*2).unwrap();
            let delta_lc: LinearCombination = (*delta).into();
            let (_, delta_inv) = derived_witnesses.get(i*2+1).unwrap();
            let delta_inv_lc = (*delta_inv).into();

            // show that delta is in fact = left - right --> left - (right + delta) = 0
            cs.constrain(left_lc - (right_lc + delta_lc.clone()));

            // multiply delta * delta_inv, if delta is non-zero this will be 1, otherwise 0
            let (_, _, delta_times_delta_inv) = cs.multiply(delta_lc, delta_inv_lc);

            let zero_or_one_lc: LinearCombination = delta_times_delta_inv.into();

            sum = sum + zero_or_one_lc;
        }

        let sum_inv: LinearCombination = (*derived_witnesses.get(derived_witnesses.len() - 1).unwrap()).1.into();

        let (_, _, sum_times_sum_inv) = cs.multiply(sum, sum_inv);

        let one: LinearCombination = LinearCombination::from(Scalar::one());

        // show that sum * sum_inv = 1
        cs.constrain(sum_times_sum_inv - one);
    }
}

impl Inequality {
    pub fn new(right_hand: Vec<LinearCombination>, right_hand_assignment: Option<Vec<Scalar>>) -> Inequality {
        Inequality {
            right_hand: right_hand,
            right_hand_assignment: right_hand_assignment
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
}