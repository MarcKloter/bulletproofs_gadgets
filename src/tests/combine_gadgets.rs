#[cfg(test)]
mod tests {
    use bulletproofs::r1cs::{Prover, Verifier, Variable};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use curve25519_dalek::ristretto::CompressedRistretto;
    use merlin::Transcript;
    use commitments::*;
    use gadget::Gadget;
    use merkle_tree::merkle_tree_gadget::{MerkleTree256, Pattern, Pattern::*};
    use bounds_check::bounds_check_gadget::BoundsCheck;
    use mimc_hash::mimc_hash_gadget::MimcHash256;
use conversions::{scalar_to_be};

    #[test]
    fn test_combine_gadgets() {
        // ---------- SETUP ----------
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(8192, 1);

        // ---------- CREATE PROVER ----------
        let mut prover_transcript = Transcript::new(b"CombinedGadgets");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        // ---------- WITNESSES ----------
        let val: Vec<u8> = vec![67];
        let (w1_scalar, w1_commitment, w1_var) = commit(&mut prover, &val);
        
        let image: Vec<u8> = vec![
            0x0c, 0xfb, 0x0c, 0x17, 0x61, 0x82, 0x11, 0xc6, 
            0x07, 0xfe, 0xbf, 0x70, 0x3a, 0xc3, 0xf3, 0x07, 
            0x8f, 0x7d, 0x96, 0x79, 0x8f, 0xae, 0x9d, 0x4a, 
            0x16, 0x82, 0xbc, 0x59, 0x2f, 0x7c, 0xb1, 0x26
        ];
        let (w2_scalar, w2_commitment, w2_var) = commit_single(&mut prover, &image);
        
        let merkle_leaf: Vec<u8> = vec![
            0x09, 0x24, 0x33, 0x33, 0xe3, 0x74, 0xe7, 0x6e, 
            0x49, 0x75, 0xab, 0x48, 0xae, 0x38, 0x24, 0x1b, 
            0xa6, 0x78, 0x05, 0xcd, 0x60, 0xf1, 0x52, 0x3e, 
            0x9b, 0x79, 0xa4, 0x8d, 0xaa, 0xc9, 0xa8, 0x4d
        ];
        let (w3_scalar, w3_commitment, w3_var) = commit_single(&mut prover, &merkle_leaf);

        let mut witness_commitments: Vec<CompressedRistretto> = Vec::new();
        witness_commitments.push(w1_commitment[0].clone());
        witness_commitments.push(w2_commitment.clone());
        witness_commitments.push(w3_commitment.clone());

        // ---------- BOUNDS ----------
        let min: Vec<u8> = vec![10];
        let max: Vec<u8> = vec![100];

        let p_bounds = BoundsCheck::new(&min, &max);
        let bounds_dc = p_bounds.prove(&mut prover, &w1_scalar, &w1_var);

        // ---------- HASH ----------
        let p_hash = MimcHash256::new(w2_var.into());
        let hash_dc = p_hash.prove(&mut prover, &w1_scalar, &w1_var);

        // ---------- MERKLE ----------
        //     I1
        //    /  \
        //  W2    W3
        let root: Vec<u8> = vec![
            0x0c, 0x8c, 0x87, 0xb6, 0x48, 0xe8, 0xfa, 0x0d, 
            0x97, 0x26, 0xee, 0x82, 0x25, 0xbe, 0x06, 0x28, 
            0x79, 0x4f, 0x2e, 0x1d, 0x1a, 0xb9, 0x32, 0x42, 
            0x1d, 0x45, 0x85, 0x1a, 0x35, 0xd8, 0x1a, 0xc1
        ];
        let pattern: Pattern = hash!(V, V);

        let p_merkle = MerkleTree256::new(&root, pattern.clone());
        let merkle_dc = p_merkle.prove(&mut prover, &vec![w2_scalar, w3_scalar], &vec![w2_var, w3_var]);

        // ---------- CREATE PROOF ----------
        let proof = prover.prove(&bp_gens).unwrap();

        // ---------- VERIFIER ----------
        let mut verifier_transcript = Transcript::new(b"CombinedGadgets");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let witness_vars: Vec<Variable> = verifier_commit(&mut verifier, witness_commitments);

        // ---------- BOUNDS ----------
        let v_bounds = BoundsCheck::new(&min, &max);
        v_bounds.verify(&mut verifier, &vec![witness_vars[0]], &bounds_dc);

        // ---------- HASH ----------
        let v_hash = MimcHash256::new(witness_vars[1].into());
        v_hash.verify(&mut verifier, &vec![witness_vars[0]], &hash_dc);

        // ---------- MERKLE ----------
        let v_merkle = MerkleTree256::new(&root, pattern.clone());
        v_merkle.verify(&mut verifier, &vec![witness_vars[1], witness_vars[2]], &merkle_dc);

        // ---------- VERIFY PROOF ----------
        let result = verifier.verify(&proof, &pc_gens, &bp_gens);
        match result {
            Ok(_) => println!("SUCESS !"),
            Err(msg) => println!("{}", msg)
        }
        //assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}