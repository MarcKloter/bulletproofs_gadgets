use bulletproofs::r1cs::{ConstraintSystem, Variable, Prover, Verifier, LinearCombination};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use gadget::Gadget;
use conversions::{vars_to_lc, be_to_scalar};
use commitments::commit_all_single;
use mimc_hash::mimc_hash_gadget::MimcHash256;

macro_rules! hash {
    ($left:expr, $right:expr) => {
        Pattern::Hash(Box::new($left), Box::new($right))
    };
}

/// Example usage: hash!(Value, hash!(Value, Value))
#[derive(Clone)]
enum Pattern {
    Hash(Box<Pattern>, Box<Pattern>),
    V
}

struct MerkleTree256 {
    root: LinearCombination,
    pattern: Pattern,
    gadget: MimcHash256
}

impl Gadget for MerkleTree256 {
    fn preprocess(&self, _: &Vec<Scalar>) -> Vec<Scalar> {
        Vec::new()
    }

    fn assemble(&self, cs: &mut ConstraintSystem, witnesses: &Vec<Variable>, _: &Vec<(Option<Scalar>, Variable)>) {
        let mut values = vars_to_lc(witnesses);
    
        let hash: LinearCombination = self.parse(cs, &mut values, self.pattern.clone());

        cs.constrain(hash - self.root.clone());
    }
}

impl MerkleTree256 {    
    fn new(root: &Vec<u8>, pattern: Pattern) -> MerkleTree256 {
        assert!(root.len() == 32, "the provided root image is not 32 bytes");

        MerkleTree256 {
            root: be_to_scalar(root).into(),
            pattern: pattern,
            gadget: MimcHash256::init()
        }
    }

    fn parse(
        &self,
        cs: &mut ConstraintSystem, 
        vals: &mut Vec<LinearCombination>,
        pattern: Pattern
    ) -> LinearCombination {
        let preimage: Vec<LinearCombination>;
        match pattern {
            Pattern::Hash(left @ box Pattern::Hash(_,_), box Pattern::V) => 
                preimage = vec![self.parse(cs, vals, *left), self.next_val(vals)],
            Pattern::Hash(box Pattern::V, right @ box Pattern::Hash(_,_)) =>
                preimage = vec![self.next_val(vals), self.parse(cs, vals, *right)],
            Pattern::Hash(left @ box Pattern::Hash(_,_), right @ box Pattern::Hash(_,_)) => 
                preimage = vec![self.parse(cs, vals, *left), self.parse(cs, vals, *right)],
            Pattern::Hash(box Pattern::V, box Pattern::V) => 
                preimage = vec![self.next_val(vals), self.next_val(vals)],
            Pattern::V => preimage = vec![self.next_val(vals)]
        }

        self.gadget.mimc_sponge(cs, &preimage)
    }

    fn next_val(&self, values: &mut Vec<LinearCombination>) -> LinearCombination {
        assert!(values.len() > 0, "too few witnesses to satisfy the provided pattern");

        values.remove(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::Pattern::*;

    const W1: [u8; 32] = [
        0x05, 0x22, 0xa6, 0x4d, 0x7b, 0x93, 0x1e, 0x21, 
        0x76, 0x0c, 0xf9, 0x55, 0xa1, 0x5f, 0xcc, 0x79, 
        0x3e, 0x8a, 0x52, 0xb4, 0x2a, 0x56, 0xab, 0x03, 
        0xaf, 0xdd, 0xec, 0x8b, 0xeb, 0x66, 0x87, 0x49
    ];
    const W2: [u8; 32] = [
        0x07, 0xfa, 0xf8, 0xaa, 0xa2, 0x10, 0x77, 0x20, 
        0x0a, 0x11, 0x57, 0x6b, 0x1c, 0xdb, 0x40, 0x2f, 
        0x52, 0xa4, 0x7f, 0x19, 0x2b, 0x36, 0x99, 0x8b, 
        0x4d, 0xa2, 0x58, 0x07, 0xa9, 0xbe, 0x52, 0xf5
    ];
    const W3: [u8; 32] = [
        0x09, 0x24, 0x33, 0x33, 0xe3, 0x74, 0xe7, 0x6e, 
        0x49, 0x75, 0xab, 0x48, 0xae, 0x38, 0x24, 0x1b, 
        0xa6, 0x78, 0x05, 0xcd, 0x60, 0xf1, 0x52, 0x3e, 
        0x9b, 0x79, 0xa4, 0x8d, 0xaa, 0xc9, 0xa8, 0x4d
    ];
    const W4: [u8; 32] = [
        0x02, 0x58, 0x64, 0x7e, 0x47, 0xe8, 0x00, 0x57, 
        0x48, 0xd4, 0xe7, 0xd0, 0xd7, 0x6b, 0x23, 0x0c, 
        0xc2, 0x0f, 0x2a, 0x0f, 0x87, 0x45, 0xee, 0xe2, 
        0xbc, 0xcc, 0xed, 0x0c, 0x2a, 0xdd, 0x59, 0xd5
    ];
    const W5: [u8; 32] = [
        0x01, 0x1c, 0x6f, 0xc7, 0xf1, 0x50, 0x87, 0xf4, 
        0xd3, 0xe9, 0x7e, 0x67, 0x28, 0x13, 0xaf, 0x06, 
        0x6f, 0x74, 0xf6, 0x04, 0x46, 0xbc, 0x75, 0xaa, 
        0x85, 0xeb, 0x2d, 0x6d, 0xb8, 0xae, 0x79, 0x1b
    ];
    const W6: [u8; 32] = [
        0x0f, 0x86, 0x53, 0xb7, 0xe7, 0x34, 0x42, 0x2f, 
        0xc7, 0x5b, 0xdb, 0x4e, 0xb1, 0xbc, 0x77, 0x4c, 
        0xd3, 0x4f, 0x9a, 0xb3, 0xa8, 0x95, 0x45, 0xe0, 
        0x21, 0x01, 0x6a, 0x4d, 0x91, 0x71, 0xa9, 0x02
    ];
    const W7: [u8; 32] = [
        0x0b, 0xd7, 0x52, 0xeb, 0x80, 0xbf, 0xa5, 0x18, 
        0x9b, 0xad, 0xe1, 0xcc, 0x8f, 0x49, 0xcf, 0x5f, 
        0xe1, 0x84, 0x3e, 0x1f, 0xf7, 0x36, 0x36, 0x7a, 
        0xfc, 0x52, 0x67, 0x0e, 0x42, 0x9d, 0x1c, 0x36
    ];
    const W8: [u8; 32] = [
        0x18, 0x1c, 0x63, 0xcf, 0xc8, 0x23, 0xa4, 0x77, 
        0xb0, 0x82, 0x50, 0x04, 0x47, 0x52, 0x22, 0xe1, 
        0xc7, 0xd0, 0x60, 0x17, 0x9b, 0x6b, 0x24, 0x7f, 
        0xfa, 0x5a, 0xdc, 0x58, 0xe3, 0x07, 0xde, 0x0d
    ];
    const W9: [u8; 32] = [
        0x2a, 0xd8, 0x4a, 0x04, 0xeb, 0x93, 0x94, 0xe0, 
        0xcc, 0x4b, 0x4b, 0x47, 0x8f, 0x21, 0x1a, 0x81, 
        0x5f, 0x27, 0x07, 0x59, 0x7c, 0x60, 0x32, 0xa9, 
        0x8a, 0x57, 0x3f, 0xbd, 0xee, 0x4a, 0x31, 0x09
    ];
    const W10: [u8; 32] = [
        0xc4, 0x5a, 0x43, 0x5f, 0x3c, 0x40, 0x1e, 0xeb, 
        0x6d, 0x3a, 0x08, 0xb2, 0xf9, 0x36, 0x69, 0xee, 
        0x33, 0xe4, 0xad, 0x26, 0x40, 0xe4, 0xe9, 0xa9, 
        0xa3, 0x49, 0x37, 0x00, 0x6a, 0xe8, 0xb3, 0x08
    ];
    const W11: [u8; 32] = [
        0xac, 0xb3, 0x32, 0x46, 0xc6, 0x95, 0x45, 0x22, 
        0x5a, 0x61, 0xfb, 0x60, 0xb4, 0x48, 0x68, 0xe8, 
        0xbc, 0x8d, 0x25, 0x53, 0x3c, 0x66, 0x3a, 0xac, 
        0xab, 0xe4, 0x49, 0x68, 0x6b, 0xbe, 0xd4, 0x0c
    ];
    const W12: [u8; 32] = [
        0x7f, 0x7e, 0xba, 0x68, 0xd7, 0xbe, 0x6b, 0x70, 
        0x76, 0xc1, 0x7b, 0x6d, 0xc4, 0x73, 0xa6, 0xd1, 
        0x77, 0x0b, 0xcf, 0x1c, 0xb4, 0x26, 0x6e, 0x7f, 
        0xb1, 0xe4, 0x64, 0x26, 0x58, 0x05, 0x06, 0x09
    ];
    const W13: [u8; 32] = [
        0xa8, 0x4d, 0x1c, 0xec, 0xeb, 0x0e, 0xbc, 0x71, 
        0x0b, 0xa2, 0xbc, 0x5a, 0xe6, 0x0b, 0xb6, 0xc3, 
        0x8a, 0xba, 0xd1, 0x5f, 0x65, 0x0b, 0xf7, 0xe8, 
        0x7c, 0xb9, 0x01, 0x53, 0x31, 0x25, 0x11, 0x0d
    ];
    const W14: [u8; 32] = [
        0x15, 0x7c, 0xdb, 0xde, 0xce, 0x96, 0x31, 0x29, 
        0x86, 0xc9, 0xf4, 0x4e, 0x03, 0xc2, 0x32, 0xd4, 
        0xca, 0x9a, 0xad, 0x55, 0xe4, 0xe2, 0x59, 0x82, 
        0x8f, 0x1a, 0xc4, 0x51, 0xa9, 0x3d, 0xd4, 0x0a
    ];
    const W15: [u8; 32] = [
        0xa3, 0x2f, 0x31, 0x8c, 0x92, 0x2b, 0x64, 0x04, 
        0xd6, 0xdd, 0x8e, 0xb2, 0xf6, 0x5a, 0x73, 0xb0, 
        0x5a, 0x49, 0xf1, 0x4c, 0xb0, 0xb1, 0x3f, 0x48, 
        0x28, 0xa8, 0x40, 0x07, 0x9e, 0x60, 0x46, 0x0d
    ];
    
    #[test]
    fn test_merkle_tree_gadget_1() {
        //                   1
        //                  / \
        //         2                  3
        //        / \                / \
        //     4        5        6        7
        //    / \      / \      / \      / \
        //   8   9   10   11  12   13  14   15

        let root: Vec<u8> = W1.to_vec();

        let pattern: Pattern = hash!(hash!(hash!(V, V), hash!(V, V)), hash!(hash!(V, V), hash!(V, V)));

        let mut witnesses: Vec<Vec<u8>> = Vec::new();
        witnesses.push(W8.to_vec());
        witnesses.push(W9.to_vec());
        witnesses.push(W10.to_vec());
        witnesses.push(W11.to_vec());
        witnesses.push(W12.to_vec());
        witnesses.push(W13.to_vec());
        witnesses.push(W14.to_vec());
        witnesses.push(W15.to_vec());

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(16384, 1);

        let mut prover_transcript = Transcript::new(b"MerkleTree");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MerkleTree256::new(&root, pattern);
        let (scalars, witness_commitments, variables) = commit_all_single(&mut prover, &witnesses);
        let derived_commitments: Vec<CompressedRistretto> = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MerkleTree");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        
        gadget.verify(&mut verifier, &witness_commitments, &derived_commitments);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_merkle_tree_gadget_2() {
        //                   1
        //                  / \
        //         2                  3
        //        / \                / \
        //     4        5        6        7
        //    / \      / \      
        //   8   9   10   11  

        let root: Vec<u8> = W1.to_vec();

        let pattern: Pattern = hash!(hash!(hash!(V, V), hash!(V, V)), hash!(V, V));

        let mut witnesses: Vec<Vec<u8>> = Vec::new();
        witnesses.push(W8.to_vec());
        witnesses.push(W9.to_vec());
        witnesses.push(W10.to_vec());
        witnesses.push(W11.to_vec());
        witnesses.push(W6.to_vec());
        witnesses.push(W7.to_vec());

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(16384, 1);

        let mut prover_transcript = Transcript::new(b"MerkleTree");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MerkleTree256::new(&root, pattern);
        let (scalars, witness_commitments, variables) = commit_all_single(&mut prover, &witnesses);
        let derived_commitments: Vec<CompressedRistretto> = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MerkleTree");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        
        gadget.verify(&mut verifier, &witness_commitments, &derived_commitments);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_merkle_tree_gadget_3() {
        //                   1
        //                  / \
        //         2                  3
        //        / \   
        //     4        5  
        //    / \      / \      
        //   8   9   10   11  

        let root: Vec<u8> = W1.to_vec();

        let pattern: Pattern = hash!(hash!(hash!(V, V), hash!(V, V)), V);

        let mut witnesses: Vec<Vec<u8>> = Vec::new();
        witnesses.push(W8.to_vec());
        witnesses.push(W9.to_vec());
        witnesses.push(W10.to_vec());
        witnesses.push(W11.to_vec());
        witnesses.push(W3.to_vec());

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(16384, 1);

        let mut prover_transcript = Transcript::new(b"MerkleTree");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MerkleTree256::new(&root, pattern);
        let (scalars, witness_commitments, variables) = commit_all_single(&mut prover, &witnesses);
        let derived_commitments: Vec<CompressedRistretto> = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MerkleTree");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        
        gadget.verify(&mut verifier, &witness_commitments, &derived_commitments);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_merkle_tree_gadget_4() {
        //                   1
        //                  / \
        //         2                  3
        //        / \                / \
        //     4        5        6        7
        //                      / \      / \
        //                    12   13  14   15

        let root: Vec<u8> = W1.to_vec();

        let pattern: Pattern = hash!(hash!(V, V), hash!(hash!(V, V), hash!(V, V)));

        let mut witnesses: Vec<Vec<u8>> = Vec::new();
        witnesses.push(W4.to_vec());
        witnesses.push(W5.to_vec());
        witnesses.push(W12.to_vec());
        witnesses.push(W13.to_vec());
        witnesses.push(W14.to_vec());
        witnesses.push(W15.to_vec());

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(16384, 1);

        let mut prover_transcript = Transcript::new(b"MerkleTree");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MerkleTree256::new(&root, pattern);
        let (scalars, witness_commitments, variables) = commit_all_single(&mut prover, &witnesses);
        let derived_commitments: Vec<CompressedRistretto> = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MerkleTree");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        
        gadget.verify(&mut verifier, &witness_commitments, &derived_commitments);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }

    #[test]
    fn test_merkle_tree_gadget_5() {
        //                   1
        //                  / \
        //         2                  3
        //                           / \
        //                       6        7
        //                      / \      / \
        //                    12   13  14   15

        let root: Vec<u8> = W1.to_vec();

        let pattern: Pattern = hash!(V, hash!(hash!(V, V), hash!(V, V)));

        let mut witnesses: Vec<Vec<u8>> = Vec::new();
        witnesses.push(W2.to_vec());
        witnesses.push(W12.to_vec());
        witnesses.push(W13.to_vec());
        witnesses.push(W14.to_vec());
        witnesses.push(W15.to_vec());

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(16384, 1);

        let mut prover_transcript = Transcript::new(b"MerkleTree");
        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let gadget = MerkleTree256::new(&root, pattern);
        let (scalars, witness_commitments, variables) = commit_all_single(&mut prover, &witnesses);
        let derived_commitments: Vec<CompressedRistretto> = gadget.prove(&mut prover, &scalars, &variables);
        let proof = prover.prove(&bp_gens).unwrap();

        let mut verifier_transcript = Transcript::new(b"MerkleTree");
        let mut verifier = Verifier::new(&mut verifier_transcript);
        
        gadget.verify(&mut verifier, &witness_commitments, &derived_commitments);
        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
    }
}