use crate::curve25519_dalek::scalar::Scalar;
use std::convert::TryInto;

/// Encodes the given byte slice as 32 byte Scalars
///
/// # Arguments
/// * `bytes` - A byte slice whose length must be a multiple of 32
pub fn to_scalars(bytes: &Vec<u8>) -> Vec<Scalar> {
    assert!((bytes.len() % 32) == 0);

    let mut scalars: Vec<Scalar> = Vec::new();

    for i in (0..bytes.len()).step_by(32) {
        // extract current u8 32 bytes block
        let _block: [u8; 32] = bytes[i..(i+32)].try_into().unwrap();

        let scalar: Scalar = Scalar::from_bytes_mod_order(_block);
        scalars.push(scalar);
    }

    scalars
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
        0xfb, 0x98, 0x7c, 0xf9, 0x7a, 0x9f, 0x1b, 0xd5, 
        0x49, 0x23, 0x47, 0xd6, 0xf4, 0xe5, 0x50, 0xae, 
        0x29, 0x49, 0xa5, 0x13, 0xde, 0x92, 0xfe, 0x50, 
        0x65, 0x35, 0x0e, 0xbc, 0xd5, 0x1d, 0xb6, 0x04
    ];

    #[test]
    fn test_bytes_to_scalars() {
        let scalars: Vec<Scalar> = to_scalars(&[BYTES_1, BYTES_2].concat()); 

        assert_eq!(&BYTES_1, scalars[0].as_bytes());
        assert_eq!(&BYTES_2, scalars[1].as_bytes());
    }
}