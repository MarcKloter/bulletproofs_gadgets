use bulletproofs::r1cs::{ConstraintSystem, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use gadget::Gadget;
use super::mimc_consts::ROUND_CONSTANTS_769;

struct MimcHash256 {
    image: Scalar,
    round_constants: Vec<Scalar>
}

impl Gadget<Vec<u8>, Vec<u8>> for MimcHash256 {
    fn new(instance_vars: &Vec<u8>) -> MimcHash256 {
        let mut round_constants: Vec<Scalar> = Vec::new();
        for constant in ROUND_CONSTANTS_769.iter() {
            round_constants.push(Scalar::from_bytes_mod_order(*constant));
        }

        MimcHash256 {
            image: Scalar::from_bytes_mod_order(slice_to_array!(&instance_vars[..32], 32)),
            round_constants: round_constants
        }
    }

    /// Encode witness variables Vec<u8> as Vec<Scalar>
    fn preprocess(&self, witness_vars: &Vec<u8>) -> Vec<Scalar> {
        let mut witness_scalar: Vec<Scalar> = Vec::new();

        let mut preimage: Vec<u8> = witness_vars.clone();
        const BLOCK_SIZE: usize = 32; // rate = 256 bits = 32 bytes
        pkcs7::pad(&mut preimage, BLOCK_SIZE as u8); // apply byte padding
        
        for i in 0..(preimage.len() / BLOCK_SIZE) {
            witness_scalar.push(Scalar::from_bytes_mod_order(slice_to_array!(&preimage[i*32..(i+1)*32], 32)));
        }

        witness_scalar
    }

    fn assemble(&self, cs: &mut ConstraintSystem, commitments: &Vec<Variable>, _: Option<Vec<Scalar>>) {
        let hash = self.mimc_sponge(cs, commitments);
    
        // constrain hash - image = 0 <=> hash = image
        let image_lc: LinearCombination = self.image.into();
        cs.constrain(hash - image_lc);
    }
}

impl MimcHash256 {
    const ROUNDS: usize = 486;

    fn mimc_sponge(
        &self,
        cs: &mut ConstraintSystem,
        preimage: &Vec<Variable>
    ) -> LinearCombination {
        let key_zero: LinearCombination = Scalar::zero().into();
        let mut state: LinearCombination = Scalar::zero().into();

        for variable in preimage {
            let var_lc: LinearCombination = (*variable).into();
            state = state + var_lc;
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

    #[test]
    fn test_mimc_hash_gadget() {
        let preimage = b"MiMCHash-256b Preimage";
        
        let image: Vec<u8> = vec![
            0xa9, 0x22, 0x53, 0x43, 0x2e, 0xa3, 0xdf, 0x78, 
            0x6c, 0xaf, 0x8a, 0x0f, 0xc0, 0x8a, 0x27, 0xbb, 
            0x28, 0x85, 0xb0, 0x35, 0x42, 0x10, 0x61, 0x25, 
            0xf7, 0x05, 0x91, 0xb3, 0x51, 0xf5, 0xf0, 0x02
        ];
        
        let instance_vars : Vec<u8> = image;
        let witness_vars : Vec<u8> = preimage.to_vec();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(4096, 1);

        let mut prover_transcript = Transcript::new(b"MiMCHash");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MimcHash256::new(&instance_vars);
        let commitments = gadget.prove(&mut prover, &witness_vars);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MiMCHash");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        
        gadget.verify(&mut verifier, &commitments);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}