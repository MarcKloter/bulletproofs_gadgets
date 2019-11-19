# bulletproofs_gadgets
[![build](https://github.com/MarcKloter/bulletproofs_gadgets/workflows/build/badge.svg)](https://github.com/MarcKloter/bulletproofs_gadgets/actions)

This repository contains r1cs gadgets to use with [dalek-cryptographys implementation of Bulletproofs](https://github.com/dalek-cryptography/bulletproofs) along with the definition of a mini-language to combine these gadgets into statements and a parser for execution. 

## Running an Example Proof
In the following we execute the example zero-knowledge proof specified in `example.gadgets` using the instance variables from `example.inst` and prover witnesses `example.wtns`. These files can be passed to the prover executable defined in `src/bin/prover.rs` using:
```
cargo run --bin prover example
```
The prover will create commitments to his secret witness variables into `example.coms` and create a r1cs proof `example.proof`. To verify the proof, we can pass those files together with the circuit specification `example.gadgets` and the public instance variables `example.inst` to the verifier executable defined in `src/bin/verifier.rs` using:
```
cargo run --bin verifier example
```

## Running Integration and Unit Tests
```
cargo test
```
