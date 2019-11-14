use crate::curve25519_dalek::scalar::Scalar;
use bulletproofs::r1cs::{Variable, LinearCombination};
use std::convert::TryInto;

/// Constructs 32 byte Scalars from the given byte vector in little endian order
pub fn le_to_scalars(bytes: &Vec<u8>) -> Vec<Scalar> {
    let mut bytes = bytes.clone();
    if bytes.len() % 32 != 0 {
        zero_padding!(bytes, 32 - (bytes.len() % 32));
    }
    
    let mut scalars: Vec<Scalar> = Vec::new();

    for i in (0..bytes.len()).step_by(32) {
        // extract current u8 32 bytes block
        let _block: [u8; 32] = bytes[i..(i+32)].try_into().unwrap();

        let scalar: Scalar = Scalar::from_bits(_block);
        scalars.push(scalar);
    }

    scalars
}

/// Constructs 32 byte Scalars from the given byte vector in big endian order
pub fn be_to_scalars(bytes: &Vec<u8>) -> Vec<Scalar> {
    let mut bytes = bytes.clone();
    bytes.reverse();
    le_to_scalars(&bytes)
}

/// Constructs a 32 byte Scalar from the given byte vector in little endian order
pub fn le_to_scalar(bytes: &Vec<u8>) -> Scalar {
    assert!(bytes.len() <= 32, "the given vector is longer than 32 bytes");

    let mut bytes: Vec<u8> = bytes.clone();
    if bytes.len() % 32 != 0 {
        zero_padding!(bytes, 32 - (bytes.len() % 32));
    }

    let _block: [u8; 32] = bytes[0..32].try_into().unwrap();

    let scalar: Scalar = Scalar::from_bits(_block);

    scalar
}

/// Constructs a 32 byte Scalar from the given byte vector in big endian order
pub fn be_to_scalar(bytes: &Vec<u8>) -> Scalar {
    let mut bytes = bytes.clone();
    bytes.reverse();
    le_to_scalar(&bytes)
}

/// Convert given byte vector in little endian order to u64
pub fn le_to_u64(bytes: &Vec<u8>) -> u64 {
    let mut bytes: Vec<u8> = bytes.clone();
    remove_zero_padding!(bytes);
    assert!(bytes.len() <= 8, "the given vec contains more than 8 non-zero le bytes");
    zero_padding!(bytes, 8 - (bytes.len() % 8));
    u64::from_le_bytes(slice_to_array!(&bytes[0..8],8))
}

/// Convert given byte vector in big endian order to u64
pub fn be_to_u64(bytes: &Vec<u8>) -> u64 {
    let mut bytes: Vec<u8> = bytes.clone();
    bytes.reverse();
    le_to_u64(&bytes)
}

/// Constructs a 32 byte Scalar from the given byte vector in big endian order
pub fn scalar_to_be(scalar: &Scalar) -> Vec<u8> {
    let mut bytes: Vec<u8> = scalar.as_bytes().to_vec();
    bytes.reverse();
    bytes
}

pub fn vars_to_lc(variables: &Vec<Variable>) -> Vec<LinearCombination> {
    let lcs: Vec<LinearCombination> = variables
        .iter()
        .map(|var| var.clone().into())
        .collect();
    
    lcs
}

pub fn scalars_to_lc(scalars: &Vec<Scalar>) -> Vec<LinearCombination> {
    let lcs: Vec<LinearCombination> = scalars
        .iter()
        .map(|scalar| scalar.clone().into())
        .collect();
    
    lcs
}

#[cfg(test)]
mod tests {
    use super::*;

    const BYTES_1: [u8; 32] = [
        0x7b, 0x24, 0x60, 0xbe, 0x18, 0x05, 0x44, 0xcd, 
        0x18, 0xe3, 0xe7, 0xe2, 0x73, 0x30, 0xce, 0xc9, 
        0x51, 0x7a, 0x31, 0x4a, 0xcb, 0xd4, 0xa0, 0x11, 
        0xd2, 0x73, 0xa5, 0x9b, 0x48, 0x0c, 0x1e, 0x00
    ];

    const BYTES_2: [u8; 32] = [
        0x7b, 0x98, 0x7c, 0xf9, 0x7a, 0x9f, 0x1b, 0xd5, 
        0x49, 0x23, 0x47, 0xd6, 0xf4, 0xe5, 0x50, 0xae, 
        0x29, 0x49, 0xa5, 0x13, 0xde, 0x92, 0xfe, 0x50, 
        0x65, 0x35, 0x0e, 0xbc, 0xd5, 0x1d, 0xb6, 0x04
    ];

    #[test]
    fn test_le_to_scalars() {
        let scalars: Vec<Scalar> = le_to_scalars(&[BYTES_1, BYTES_2].concat());

        assert_eq!(&BYTES_1, scalars[0].as_bytes());
        assert_eq!(&BYTES_2, scalars[1].as_bytes());
    }

    #[test]
    fn test_le_to_scalar() {
        let scalar: Scalar = le_to_scalar(&BYTES_1.to_vec());

        assert_eq!(&BYTES_1, scalar.as_bytes());
    }

    #[test]
    fn test_be_to_scalar() {
        let scalar: Scalar = be_to_scalar(&BYTES_1.to_vec());

        let mut bytes = BYTES_1.to_vec();
        bytes.reverse();
        
        assert_eq!(&bytes, scalar.as_bytes());
    }

    #[test]
    fn test_be_to_scalars() {
        let scalars: Vec<Scalar> = be_to_scalars(&[BYTES_1, BYTES_2].concat());

        let mut bytes1 = BYTES_1.to_vec();
        bytes1.reverse();
        let mut bytes2 = BYTES_2.to_vec();
        bytes2.reverse();

        assert_eq!(&bytes2, scalars[0].as_bytes());
        assert_eq!(&bytes1, scalars[1].as_bytes());
    }

}