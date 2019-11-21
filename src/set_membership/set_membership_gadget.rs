use bulletproofs::r1cs::{ConstraintSystem, Variable, LinearCombination};
use curve25519_dalek::scalar::Scalar;
use gadget::Gadget;

pub struct SetMembership {
    value: LinearCombination,
    value_assignment: Option<Scalar>,
    instance_vars: Vec<LinearCombination>,
    instance_vars_assignments: Option<Vec<Scalar>>
}

impl Gadget for SetMembership {
    fn preprocess(&self, witnesses: &Vec<Scalar>) -> Vec<Scalar> {
        assert!(self.value_assignment.is_some(), "missing value assignment");
        assert!(self.instance_vars_assignments.is_some(), "missing instance vars assignments");

        let instance_vars_assignments = self.instance_vars_assignments.as_ref().unwrap();
        let mut set: Vec<Scalar> = Vec::new();
        for e in witnesses { set.push(e.clone()); }
        for e in instance_vars_assignments { set.push(e.clone()); }
        
        let mut derived_witnesses: Vec<Scalar> = Vec::new();
        let value: Scalar = self.value_assignment.unwrap();
        // create one hot vector for the value in the set
        for element in set {
            if element == value {
                derived_witnesses.push(Scalar::one());
            } else {
                derived_witnesses.push(Scalar::zero()); 
            }
        }
        
        derived_witnesses
    }

    fn assemble(
        &self, 
        cs: &mut dyn ConstraintSystem, 
        witnesses: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) {
        let mut one_hot_vector = Vec::new();
        for (_, bit) in derived_witnesses {
            let bit_lc: LinearCombination = LinearCombination::from(*bit);

            // show that these derived witnesses are bits
            self.is_bit(cs, bit_lc.clone());

            one_hot_vector.push(bit_lc);
        }

        // show that the bit vector from derived witnesses is one-hot
        self.one_hot_vector(cs, one_hot_vector.clone());

        let mut set: Vec<LinearCombination> = Vec::new();
        for w in witnesses { set.push(LinearCombination::from(*w)); }
        for e in self.instance_vars.clone() { set.push(e.clone()); }
        
        // show that the element that is marked by the one-hot vector is equal to the value
        self.hadamard_product(cs, one_hot_vector, set, self.value.clone());
    }
}

impl SetMembership {
    pub fn new(
        value: LinearCombination,
        value_assignment: Option<Scalar>,
        instance_vars: Vec<LinearCombination>,
        instance_vars_assignments: Option<Vec<Scalar>>
    ) -> SetMembership {
        SetMembership {
            value,
            value_assignment,
            instance_vars,
            instance_vars_assignments
        }
    }

    /// ensures that the given `vec` is one-hot (all bits are 0 with a single bit set to 1)
    fn one_hot_vector(
        &self, 
        cs: &mut dyn ConstraintSystem,
        vector: Vec<LinearCombination>
    ) {
        let mut sum: LinearCombination = Scalar::zero().into();

        for bit in vector {
            sum = sum + bit;
        }

        let one: LinearCombination = Scalar::one().into();

        // show that the one-hot vector sum is 1
        cs.constrain(one - sum);
    }

    /// ensures that the given `bit` is either 0 or 1
    fn is_bit(
        &self, 
        cs: &mut dyn ConstraintSystem,
        bit: LinearCombination
    ) { 
        let one: LinearCombination = Scalar::one().into();
        let one_minus_bit: LinearCombination = one - bit.clone();

        // show that either bit or (1 - bit) is 0
        let (_, _, should_be_zero) = cs.multiply(one_minus_bit.clone(), bit.clone());
        
        cs.constrain(should_be_zero.into());
    }

    fn hadamard_product(
        &self, 
        cs: &mut dyn ConstraintSystem,
        vec_one: Vec<LinearCombination>,
        vec_two: Vec<LinearCombination>,
        expected_product: LinearCombination
    ) {
        if vec_one.len() != vec_two.len() {
            return cs.constrain(Scalar::one().into());
        }

        let mut actual_product: LinearCombination = Scalar::zero().into();
        for index in 0..vec_one.len() {
            let (_, _, product) = cs.multiply(vec_one.get(index).unwrap().clone(), vec_two.get(index).unwrap().clone());
            actual_product = actual_product.clone() + LinearCombination::from(product);
        }
        
        // show that the hadamard product of the two given vectors is equal to the expected product
        cs.constrain(expected_product - actual_product);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use commitments::{commit_all_single, commit_single, verifier_commit};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use conversions::{be_to_scalar, scalars_to_lc};
    use bulletproofs::r1cs::{Prover, Verifier};

    const VALUE1: [u8; 32] = [
        0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
        0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
        0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
        0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49
    ];
    const VALUE2: [u8; 32] = [
        0x07, 0xfa, 0xf8, 0xaa, 0xa2, 0x10, 0x77, 0x20, 
        0x0a, 0x11, 0x57, 0x6b, 0x1c, 0xdb, 0x40, 0x2f, 
        0x52, 0xa4, 0x7f, 0x19, 0x2b, 0x36, 0x99, 0x8b, 
        0x4d, 0xa2, 0x58, 0x07, 0xa9, 0xbe, 0x52, 0xf5
    ];
    const VALUE3: [u8; 32] = [
        0x09, 0x24, 0x33, 0x33, 0xe3, 0x74, 0xe7, 0x6e, 
        0x49, 0x75, 0xab, 0x48, 0xae, 0x38, 0x24, 0x1b, 
        0xa6, 0x78, 0x05, 0xcd, 0x60, 0xf1, 0x52, 0x3e, 
        0x9b, 0x79, 0xa4, 0x8d, 0xaa, 0xc9, 0xa8, 0x4d
    ];
    const VALUE4: [u8; 32] = [
        0x02, 0x58, 0x64, 0x7e, 0x47, 0xe8, 0x00, 0x57, 
        0x48, 0xd4, 0xe7, 0xd0, 0xd7, 0x6b, 0x23, 0x0c, 
        0xc2, 0x0f, 0x2a, 0x0f, 0x87, 0x45, 0xee, 0xe2, 
        0xbc, 0xcc, 0xed, 0x0c, 0x2a, 0xdd, 0x59, 0xd5
    ];
    const VALUE5: [u8; 32] = [
        0x01, 0x1c, 0x6f, 0xc7, 0xf1, 0x50, 0x87, 0xf4, 
        0xd3, 0xe9, 0x7e, 0x67, 0x28, 0x13, 0xaf, 0x06, 
        0x6f, 0x74, 0xf6, 0x04, 0x46, 0xbc, 0x75, 0xaa, 
        0x85, 0xeb, 0x2d, 0x6d, 0xb8, 0xae, 0x79, 0x1b
    ];

    /// Test set of instance variables
    #[test]
    fn test_set_membership_gadget_1() {
        let witness_value = VALUE1.to_vec();
        let instance_set = vec![
            be_to_scalar(&VALUE4.to_vec()), 
            be_to_scalar(&VALUE3.to_vec()), 
            be_to_scalar(&VALUE1.to_vec()), 
            be_to_scalar(&VALUE5.to_vec()), 
            be_to_scalar(&VALUE2.to_vec())
        ];
        let instance_set_assignment = scalars_to_lc(&instance_set);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 1);

        let mut prover_transcript = Transcript::new(b"SetMembership");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (witness_assignment, witness_commitment, witness_var) = commit_single(&mut prover, &witness_value);
        let gadget_prover = SetMembership::new(witness_var.into(), Some(witness_assignment), instance_set_assignment.clone(), Some(instance_set));
        let (derived_commitments, derived_witnesses) = gadget_prover.setup(&mut prover, &Vec::new());
        gadget_prover.prove(&mut prover, &Vec::new(), &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"SetMembership");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, vec![witness_commitment]);
        let gadget_verifier = SetMembership::new(witness_vars[0].into(), None, instance_set_assignment, None);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget_verifier.verify(&mut verifier, &Vec::new(), &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    /// Test mixed set
    #[test]
    fn test_set_membership_gadget_2() {
        let witness_value = VALUE1.to_vec();
        let witness_set = vec![
            VALUE3.to_vec(), 
            VALUE5.to_vec(), 
            VALUE1.to_vec()
        ];
        let instance_set = vec![
            be_to_scalar(&VALUE4.to_vec()), 
            be_to_scalar(&VALUE2.to_vec())
        ];
        let instance_set_assignment = scalars_to_lc(&instance_set);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 1);

        let mut prover_transcript = Transcript::new(b"SetMembership");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (witness_assignment, witness_commitment, witness_var) = commit_single(&mut prover, &witness_value);
        let gadget_prover = SetMembership::new(witness_var.into(), Some(witness_assignment), instance_set_assignment.clone(), Some(instance_set));
        let (witness_set_assignments, witness_set_commitments, witness_set_vars) = commit_all_single(&mut prover, &witness_set);
        let (derived_commitments, derived_witnesses) = gadget_prover.setup(&mut prover, &witness_set_assignments);
        gadget_prover.prove(&mut prover, &witness_set_vars, &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"SetMembership");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, vec![witness_commitment]);
        let gadget_verifier = SetMembership::new(witness_vars[0].into(), None, instance_set_assignment, None);
        let witness_set_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_set_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget_verifier.verify(&mut verifier, &witness_set_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    /// Test mixed set, where the value is not member
    #[test]
    fn test_set_membership_gadget_3() {
        let witness_value = VALUE1.to_vec();
        let witness_set = vec![
            VALUE3.to_vec(), 
            VALUE5.to_vec()
        ];
        let instance_set = vec![
            be_to_scalar(&VALUE4.to_vec()), 
            be_to_scalar(&VALUE2.to_vec())
        ];
        let instance_set_assignment = scalars_to_lc(&instance_set);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 1);

        let mut prover_transcript = Transcript::new(b"SetMembership");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (witness_assignment, witness_commitment, witness_var) = commit_single(&mut prover, &witness_value);
        let gadget_prover = SetMembership::new(witness_var.into(), Some(witness_assignment), instance_set_assignment.clone(), Some(instance_set));
        let (witness_set_assignments, witness_set_commitments, witness_set_vars) = commit_all_single(&mut prover, &witness_set);
        let (derived_commitments, derived_witnesses) = gadget_prover.setup(&mut prover, &witness_set_assignments);
        gadget_prover.prove(&mut prover, &witness_set_vars, &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"SetMembership");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, vec![witness_commitment]);
        let gadget_verifier = SetMembership::new(witness_vars[0].into(), None, instance_set_assignment, None);
        let witness_set_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_set_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget_verifier.verify(&mut verifier, &witness_set_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    /// Test mixed set, where a witness is set to 0
    #[test]
    fn test_set_membership_gadget_4() {
        let witness_value = VALUE1.to_vec();
        let witness_set = vec![
            VALUE3.to_vec(), 
            VALUE5.to_vec(), 
            vec![0x00],
            VALUE2.to_vec()
        ];
        let instance_set = vec![
            be_to_scalar(&VALUE4.to_vec()), 
            be_to_scalar(&VALUE2.to_vec())
        ];
        let instance_set_assignment = scalars_to_lc(&instance_set);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 1);

        let mut prover_transcript = Transcript::new(b"SetMembership");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (witness_assignment, witness_commitment, witness_var) = commit_single(&mut prover, &witness_value);
        let gadget_prover = SetMembership::new(witness_var.into(), Some(witness_assignment), instance_set_assignment.clone(), Some(instance_set));
        let (witness_set_assignments, witness_set_commitments, witness_set_vars) = commit_all_single(&mut prover, &witness_set);
        let (derived_commitments, derived_witnesses) = gadget_prover.setup(&mut prover, &witness_set_assignments);
        gadget_prover.prove(&mut prover, &witness_set_vars, &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"SetMembership");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, vec![witness_commitment]);
        let gadget_verifier = SetMembership::new(witness_vars[0].into(), None, instance_set_assignment, None);
        let witness_set_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_set_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget_verifier.verify(&mut verifier, &witness_set_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    /// Test mixed set, where the value is contained twice
    #[test]
    fn test_set_membership_gadget_5() {
        let witness_value = VALUE1.to_vec();
        let witness_set = vec![
            VALUE3.to_vec(), 
            VALUE1.to_vec(), 
            VALUE5.to_vec()
        ];
        let instance_set = vec![
            be_to_scalar(&VALUE4.to_vec()), 
            be_to_scalar(&VALUE2.to_vec()), 
            be_to_scalar(&VALUE1.to_vec())
        ];
        let instance_set_assignment = scalars_to_lc(&instance_set);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 1);

        let mut prover_transcript = Transcript::new(b"SetMembership");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (witness_assignment, witness_commitment, witness_var) = commit_single(&mut prover, &witness_value);
        let gadget_prover = SetMembership::new(witness_var.into(), Some(witness_assignment), instance_set_assignment.clone(), Some(instance_set));
        let (witness_set_assignments, witness_set_commitments, witness_set_vars) = commit_all_single(&mut prover, &witness_set);
        let (derived_commitments, derived_witnesses) = gadget_prover.setup(&mut prover, &witness_set_assignments);
        gadget_prover.prove(&mut prover, &witness_set_vars, &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"SetMembership");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, vec![witness_commitment]);
        let gadget_verifier = SetMembership::new(witness_vars[0].into(), None, instance_set_assignment, None);
        let witness_set_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_set_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget_verifier.verify(&mut verifier, &witness_set_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err());
    }

    /// Test mixed set for zero member
    #[test]
    fn test_set_membership_gadget_6() {
        let witness_value = vec![0x00];
        let witness_set = vec![
            VALUE3.to_vec(), 
            VALUE5.to_vec(), 
            vec![0x00],
            VALUE1.to_vec()
        ];
        let instance_set = vec![
            be_to_scalar(&VALUE4.to_vec()), 
            be_to_scalar(&VALUE2.to_vec())
        ];
        let instance_set_assignment = scalars_to_lc(&instance_set);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 1);

        let mut prover_transcript = Transcript::new(b"SetMembership");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (witness_assignment, witness_commitment, witness_var) = commit_single(&mut prover, &witness_value);
        let gadget_prover = SetMembership::new(witness_var.into(), Some(witness_assignment), instance_set_assignment.clone(), Some(instance_set));
        let (witness_set_assignments, witness_set_commitments, witness_set_vars) = commit_all_single(&mut prover, &witness_set);
        let (derived_commitments, derived_witnesses) = gadget_prover.setup(&mut prover, &witness_set_assignments);
        gadget_prover.prove(&mut prover, &witness_set_vars, &derived_witnesses);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"SetMembership");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, vec![witness_commitment]);
        let gadget_verifier = SetMembership::new(witness_vars[0].into(), None, instance_set_assignment, None);
        let witness_set_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_set_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget_verifier.verify(&mut verifier, &witness_set_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}