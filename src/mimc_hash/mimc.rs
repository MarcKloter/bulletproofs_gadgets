use crate::curve25519_dalek::scalar::Scalar;
use crate::pkcs7;
use super::mimc_consts::ROUND_CONSTANTS_769;
use conversions::{be_to_scalars, le_to_scalar,scalar_to_be};

/// MiMC block cipher
fn mimc_encryption(
    p: &Scalar,
    k: &Scalar,
    rounds: usize,
    constants: &Vec<Scalar>
) -> Scalar {
    let mut state = p.clone();

    for i in 0..rounds {
        // p := (p + k + c[i])^3
        let tmp = state + (k + constants[i]);
        state = (tmp * tmp) * tmp;
    }

    // p := p + k
    state + k
}

/// MiMC hash in sponge mode from Markus Schofnegger
fn mimc_sponge_1(
    preimage: &Vec<Scalar>,
    rounds: usize,
    constants: &Vec<Scalar>
) -> Scalar {
    let key_zero = Scalar::zero();
    let mut state = Scalar::zero();

    for i in 0..preimage.len() {
        state += preimage[i];
        state = mimc_encryption(&state, &key_zero, rounds, constants);
    }

    state
}

/// MiMC hash in Miyaguchi–Preneel sponge mode (alternative)
fn mimc_sponge_2(
    preimage: &Vec<Scalar>,
    rounds: usize,
    constants: &Vec<Scalar>
) -> Scalar {
    let mut key = Scalar::zero();
    let mut state;

    for scalar in preimage {
        state = mimc_encryption(&scalar, &key, rounds, constants);
        key = key + scalar + state;
    }

    key
}

/// MiMCHash-256b, rate = 256, capacity = 513
pub fn mimc_hash(preimage: &Vec<u8>) -> Scalar {
    let mut preimage: Vec<Scalar> = be_to_scalars(preimage);
    pad(&mut preimage);

    // rounds = ceil((rate + capacity) / log_2(3)) = 486
    const NUM_ROUNDS: usize = 486;
    
    let mut round_constants: Vec<Scalar> = Vec::new();
    for constant in ROUND_CONSTANTS_769.iter() {
            round_constants.push(Scalar::from_bits(*constant));
    }

    // use constants according to n = rate + capacity = 769
    mimc_sponge_1(&preimage, NUM_ROUNDS, &round_constants)
}

fn pad(preimage: &mut Vec<Scalar>) {
    let last_block: Scalar = *preimage.last().unwrap();
    let mut last_block_le: Vec<u8> = Vec::new();
    last_block_le.extend(last_block.as_bytes().to_vec());
    remove_zero_padding!(last_block_le);

    const BLOCK_SIZE: usize = 32; // rate = 256 bits = 32 bytes

    let padded_block: Scalar;
    if last_block_le.len() < BLOCK_SIZE {
        // happy case: last block is PKCS#7 padded
        let mut last_block_le_padded: Vec<u8> = last_block_le.clone();
        pkcs7::pad(&mut last_block_le_padded, BLOCK_SIZE as u8); // apply byte padding
        padded_block = le_to_scalar(&last_block_le_padded);
        preimage.pop();
    } else {
        // edge case: additional block is added
        padded_block = le_to_scalar(&vec![32u8; 32]);
    }
    preimage.push(padded_block);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mimc_hash_256b_1() {
        let preimage: Vec<u8> = vec![
            0x38, 0x53, 0x54, 0x50, 0x43, 0x30, 0x43, 0x54, 
            0x6f, 0x31, 0x38, 0x77, 0x61, 0x5a, 0x6a, 0x42, 
            0x36, 0x63
        ];
        
        let expected_image: Vec<u8> = vec![
            0x0d, 0x22, 0x03, 0x06, 0x9a, 0xc1, 0x5f, 0x58, 
            0x17, 0x2b, 0xae, 0x1b, 0x3a, 0xf9, 0x8d, 0x89, 
            0x82, 0xde, 0xef, 0x9d, 0xf3, 0x74, 0x82, 0xc1, 
            0xa9, 0x20, 0xb8, 0x83, 0x2e, 0xe8, 0x13, 0xa4
        ];

        let image: Scalar = mimc_hash(&preimage);
        
        assert_eq!(&expected_image, &scalar_to_be(&image));
    }

    #[test]
    fn test_mimc_hash_256b_2() {
        let preimage: Vec<u8> = vec![
            0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x63, 
            0x6b, 0x20, 0x62, 0x72, 0x6f, 0x77, 0x6e, 0x20, 
            0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70, 
            0x73, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x20, 0x74
        ];
        
        let expected_image: Vec<u8> = vec![
            0x01, 0x24, 0x54, 0x09, 0xf2, 0x8a, 0xe2, 0xf0, 
            0x76, 0x07, 0x7d, 0x4a, 0x40, 0xbd, 0x91, 0x55, 
            0x1b, 0x3a, 0x03, 0xb1, 0xad, 0x8a, 0xdb, 0x2b, 
            0x1d, 0xa1, 0x16, 0xd2, 0x9c, 0x60, 0xa8, 0x5c
        ];

        let image: Scalar = mimc_hash(&preimage);
        
        assert_eq!(&expected_image, &scalar_to_be(&image));
    }
}