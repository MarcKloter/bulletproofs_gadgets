use crate::curve25519_dalek::scalar::Scalar;
use crate::pkcs7;

use super::mimc_consts::{ROUND_CONSTANTS_769};

use conversions::{to_scalars};

/// MiMC block cipher
fn mimc_encryption(
    p: &Scalar,
    k: &Scalar,
    rounds: usize,
    constants: &[[u8; 32]]
) -> Scalar {
    assert_eq!(constants.len(), rounds);

    let mut state = p.clone();

    for i in 0..rounds {
        // p := (p + k + c[i])^3
        let tmp = state + (k + Scalar::from_bytes_mod_order(constants[i]));
        state = (tmp * tmp) * tmp;
    }

    // p := p + k
    state + k
}

/// MiMC hash in sponge mode from Markus Schofnegger
fn mimc_sponge_1(
    preimage: &[Scalar],
    rounds: usize,
    constants: &[[u8; 32]]
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
    preimage: &[Scalar],
    rounds: usize,
    constants: &[[u8; 32]]
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
    let mut preimage = preimage.clone();

    const BLOCK_SIZE: usize = 32; // rate = 256 bits = 32 bytes

    // apply byte padding
    pkcs7::pad(&mut preimage, BLOCK_SIZE as u8);
    assert_eq!(preimage.len() % BLOCK_SIZE, 0);

    // rounds = ceil((rate + capacity) / log_2(3)) = 486
    const NUM_ROUNDS: usize = 486;

    // use constants according to n = rate + capacity = 769
    mimc_sponge_1(&to_scalars(&preimage), NUM_ROUNDS, &ROUND_CONSTANTS_769)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mimc_hash() {
        let preimage = b"MiMCHash-256b Preimage";
        
        let expected_image: [u8; 32] = [
            0xa9, 0x22, 0x53, 0x43, 0x2e, 0xa3, 0xdf, 0x78, 
            0x6c, 0xaf, 0x8a, 0x0f, 0xc0, 0x8a, 0x27, 0xbb, 
            0x28, 0x85, 0xb0, 0x35, 0x42, 0x10, 0x61, 0x25, 
            0xf7, 0x05, 0x91, 0xb3, 0x51, 0xf5, 0xf0, 0x02
        ];

        let image: Scalar = mimc_hash(&preimage.to_vec()); 
        
        assert_eq!(&expected_image, image.as_bytes());
    }
}