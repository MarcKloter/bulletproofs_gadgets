use bulletproofs::r1cs::{ConstraintSystem, Variable, LinearCombination};
use curve25519_dalek::scalar::Scalar;
use gadget::Gadget;
use conversions::{le_to_scalar, vars_to_lc};
use super::mimc_consts::ROUND_CONSTANTS_769;

pub struct MimcHash256 {
    image: LinearCombination,
    round_constants: Vec<Scalar>
}

impl Gadget for MimcHash256 {
    /// Apply byte padding to the witness (last block)
    /// Derive the block and the padding to prove that the padding was done honestly 
    fn preprocess(&self, witnesses: &Vec<Scalar>) -> Vec<Scalar> {
        let mut derived_witnesses: Vec<Scalar> = Vec::new();

        let last_block: Scalar = *witnesses.last().unwrap();
        let mut last_block_le: Vec<u8> = Vec::new();
        last_block_le.extend(last_block.as_bytes().to_vec());
        remove_zero_padding!(last_block_le);
        
        if last_block_le.len() < MimcHash256::BLOCK_SIZE {
            // happy case: last block is PKCS#7 padded
            let mut last_block_le_padded: Vec<u8> = last_block_le.clone();
            pkcs7::pad(&mut last_block_le_padded, MimcHash256::BLOCK_SIZE as u8); // apply byte padding
            let padded_block: Scalar = le_to_scalar(&last_block_le_padded);
            derived_witnesses.push(padded_block);
            derived_witnesses.push(padded_block - last_block);
        } else {
            // edge case: additional block is added
            let padding: Scalar = le_to_scalar(&vec![32u8; 32]);
            derived_witnesses.push(padding);
        }

        derived_witnesses
    }

    fn assemble(
        &self, 
        cs: &mut ConstraintSystem, 
        witnesses: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) {
        let commitments: Vec<Variable> = self.pad(cs, witnesses, derived_witnesses);
        let hash_lc: LinearCombination = self.mimc_sponge(cs, &vars_to_lc(&commitments));
    
        // constrain hash - image = 0 <=> hash = image
        cs.constrain(hash_lc - self.image.clone());
    }
}

/// MiMCHash-256b, rate = 256, capacity = 513
impl MimcHash256 {
    // rounds = ceil((rate + capacity) / log_2(3)) = 486
    const ROUNDS: usize = 486;
    const BLOCK_SIZE: usize = 32; // rate = 256 bits = 32 bytes

    pub fn init() -> MimcHash256 {
        MimcHash256 {
            image: Scalar::zero().into(),
            round_constants: MimcHash256::get_round_constants()
        }
    }

    pub fn new(image: LinearCombination) -> MimcHash256 {
        MimcHash256 {
            image: image,
            round_constants: MimcHash256::get_round_constants()
        }
    }

    pub fn get_round_constants() -> Vec<Scalar> {
        let mut round_constants: Vec<Scalar> = Vec::new();
        for constant in ROUND_CONSTANTS_769.iter() {
            round_constants.push(Scalar::from_bits(*constant));
        }
        round_constants
    }

    fn pad(
        &self, 
        cs: &mut ConstraintSystem, 
        witnesses: &Vec<Variable>, 
        derived_witnesses: &Vec<(Option<Scalar>, Variable)>
    ) -> Vec<Variable> {
        let mut commitments: Vec<Variable> = Vec::new();
        commitments.extend(witnesses);
        
        let (_, padded_block) = derived_witnesses[0];

        if derived_witnesses.len() == 2 {
            // happy case: replace last witness with its padded form
            let (_, padding) = derived_witnesses[1];
            let last_block: LinearCombination = commitments.pop().unwrap().into();
            let padding_lc: LinearCombination = padding.into();
            let last_block_plus_padding: LinearCombination = last_block.clone() + padding_lc.clone();
            let padded_block_lc: LinearCombination = padded_block.into();
            // constrain honest padding: (last_block + padding) - padded_block = 0
            cs.constrain(last_block_plus_padding - padded_block_lc);
        }
        
        commitments.push(padded_block);

        commitments
    }

    pub fn mimc_sponge(
        &self,
        cs: &mut ConstraintSystem,
        preimage: &Vec<LinearCombination>
    ) -> LinearCombination {
        let key_zero: LinearCombination = Scalar::zero().into();
        let mut state: LinearCombination = Scalar::zero().into();

        for variable in preimage {
            state = state + variable.clone();
            state = self.mimc_encryption(cs, state, key_zero.clone());
        }

        state
    }

    fn mimc_encryption(
        &self,
        cs: &mut ConstraintSystem,
        p: LinearCombination,
        k: LinearCombination
    ) -> LinearCombination {
        let mut p_v = p;
        let k_v = k;

        for i in 0..MimcHash256::ROUNDS {
            // p := (p + k + c[i])^3
            let ci_lc: LinearCombination = self.round_constants[i].into(); 

            let p_plus_k: LinearCombination = p_v.clone() + k_v.clone();
            let p_plus_k_plus_ci: LinearCombination = p_plus_k + ci_lc;

            let (x_k_ci, _, sqr) = cs.multiply(p_plus_k_plus_ci.clone(), p_plus_k_plus_ci);
            let (_, _, cube) = cs.multiply(sqr.into(), x_k_ci.into());

            p_v = LinearCombination::from(cube);
        }

        // p := p + k
        p_v = p_v + k_v;
        
        p_v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use commitments::{commit, verifier_commit};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use conversions::{be_to_scalar};
    use bulletproofs::r1cs::{Prover, Verifier};

    #[test]
    fn test_mimc_hash_gadget_1() {
        let preimage: Vec<u8> = vec![
            0x38, 0x53, 0x54, 0x50, 0x43, 0x30, 0x43, 0x54, 
            0x6f, 0x31, 0x38, 0x77, 0x61, 0x5a, 0x6a, 0x42, 
            0x36, 0x63
        ];

        let image: Scalar = be_to_scalar(&vec![
            0x0d, 0x22, 0x03, 0x06, 0x9a, 0xc1, 0x5f, 0x58, 
            0x17, 0x2b, 0xae, 0x1b, 0x3a, 0xf9, 0x8d, 0x89, 
            0x82, 0xde, 0xef, 0x9d, 0xf3, 0x74, 0x82, 0xc1, 
            0xa9, 0x20, 0xb8, 0x83, 0x2e, 0xe8, 0x13, 0xa4
        ]);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(1024, 1);

        let mut prover_transcript = Transcript::new(b"MiMCHash");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MimcHash256::new(image.into());
        let (scalars, witness_commitments, variables) = commit(&mut prover, &preimage);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MiMCHash");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_mimc_hash_gadget_2() {
        let preimage: Vec<u8> = vec![
            0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x63, 
            0x6b, 0x20, 0x62, 0x72, 0x6f, 0x77, 0x6e, 0x20, 
            0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70, 
            0x73, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x20, 0x74
        ];

        let image: Scalar = be_to_scalar(&vec![
            0x01, 0x24, 0x54, 0x09, 0xf2, 0x8a, 0xe2, 0xf0, 
            0x76, 0x07, 0x7d, 0x4a, 0x40, 0xbd, 0x91, 0x55, 
            0x1b, 0x3a, 0x03, 0xb1, 0xad, 0x8a, 0xdb, 0x2b, 
            0x1d, 0xa1, 0x16, 0xd2, 0x9c, 0x60, 0xa8, 0x5c
        ]);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let mut prover_transcript = Transcript::new(b"MiMCHash");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MimcHash256::new(image.into());
        let (scalars, witness_commitments, variables) = commit(&mut prover, &preimage);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MiMCHash");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_mimc_hash_gadget_3() {
        let preimage: Vec<u8> = vec![
            0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x4a, 
            0x76, 0x07, 0x7d, 0x4a, 0x40, 0xbd, 0x91, 0x55, 
            0x1b, 0x3a, 0x03, 0xb1, 0xad, 0x8a, 0xdb, 0x2b, 
            0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70, 
            0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70, 
            0x73, 0x20, 0x6f, 0x76, 0x65
        ];

        let image: Scalar = be_to_scalar(&vec![
            0x0f, 0xcb, 0x21, 0xfb, 0xf2, 0x3b, 0x96, 0x8d, 
            0xee, 0x8f, 0x6b, 0x3a, 0x51, 0x1e, 0x93, 0xe8, 
            0xc5, 0xc0, 0xeb, 0x2f, 0x71, 0xaa, 0x06, 0x01, 
            0x11, 0x1f, 0x91, 0x1c, 0x9e, 0x42, 0xcf, 0x06
        ]);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let mut prover_transcript = Transcript::new(b"MiMCHash");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MimcHash256::new(image.into());
        let (scalars, witness_commitments, variables) = commit(&mut prover, &preimage);
        let derived_commitments = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MiMCHash");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);
        let derived_vars: Vec<Variable> = verifier_commit(&mut verifier, derived_commitments);
        
        gadget.verify(&mut verifier, &witness_vars, &derived_vars);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}
