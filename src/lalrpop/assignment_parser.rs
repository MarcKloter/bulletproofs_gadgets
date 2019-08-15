use lalrpop::ast::*;
use commitments::commit;

use bulletproofs::r1cs::{Verifier, Prover, Variable};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

use std::collections::HashMap;
use std::io::prelude::*;
use std::io::BufReader;
use std::fs::File;

// lalrpop parsers
lalrpop_mod!(var_grammar, "/lalrpop/var_grammar.rs");

const INSTANCE_VARS_EXT: &str = ".inst";
const WITNESS_VARS_EXT: &str = ".wtns";
const COMMITMENTS_EXT: &str = ".coms";

pub struct Assignments {
    commitments: HashMap<String, Variable>,
    witness_vars: HashMap<String, (Vec<Scalar>, Vec<CompressedRistretto>, Vec<Variable>)>,
    instance_vars: HashMap<String, Vec<u8>>
}

impl Assignments {
    pub fn new() -> Assignments {
        Assignments {
            commitments: HashMap::new(),
            witness_vars: HashMap::new(),
            instance_vars: HashMap::new()
        }
    }

    fn set_instance(&mut self, key: String, val: Vec<u8>) {
        self.instance_vars.insert(key, val);
    }
    
    fn set_commitment(&mut self, key: String, val: Variable) {
        self.commitments.insert(key, val);
    }

    pub fn get_commitment(&self, var: Var, index: usize) -> Variable {
        match self.inquire_commitment(var, index) {
            Ok(commitment) => commitment,
            Err(message) => panic!(message)
        }
    }

    pub fn get_all_commitments(&self, var: Var) -> Vec<Variable> {
        let mut variables = Vec::new();

        let mut index = 0;
        while {
            let result = self.inquire_commitment(var.clone(), index);
            match result.clone() {
                Ok(witness) => variables.push(witness),
                Err(_) => ()
            }
            index += 1;

            result.is_ok()
        } {}

        variables
    }

    fn inquire_commitment(&self, var: Var, index: usize) -> Result<Variable, String> {
        match var {
            Var::Witness(name) => {
                let key = format!("C{}-{}", &name[1..name.len()], index);
                match self.commitments.get(&key) {
                    Some(commitment) => Ok(*commitment),
                    None => Err(format!("missing commitment {}", &key))
                }
            }
            _ => Err(String::from("provided variable is not of type witness"))
        }
    }

    pub fn get_derived(&self, gadget: usize, index: usize) -> Variable {
        let key = format!("D{}-{}", gadget, index);
        *self.commitments.get(&key).expect(&format!("missing commitment {}", &key))
    }

    pub fn get_instance(&self, var: Var, assertion: Option<&Fn(String, &Vec<u8>)>) -> Vec<u8> {
        match var {
            Var::Instance(name) => {
                let error = &format!("missing instance var {}", &name);
                let assignment = self.instance_vars.get(&name).expect(error).to_vec();
                match assertion {
                    Some(fnc) => fnc(name, &assignment),
                    None => ()
                }
                assignment
            }
            _ => panic!("provided variable is not of type instance")
        }
    }

    pub fn get_witness(
        &self, 
        var: Var, 
        assertion: Option<&Fn(String, &(Vec<Scalar>, Vec<CompressedRistretto>, Vec<Variable>))>
    ) -> (Vec<Scalar>, Vec<CompressedRistretto>, Vec<Variable>) {
        match var {
            Var::Witness(name) => {
                let error = &format!("missing witness var {}", &name);
                let assignment = self.witness_vars.get(&name).expect(error);
                match assertion {
                    Some(fnc) => fnc(name, &assignment),
                    None => ()
                }
                assignment.clone()
            }
            _ => panic!("provided variable is not of type witness")
        }
    }

    /// read instance variables from .inst file
    pub fn parse_inst(&mut self, filename: String) -> std::io::Result<()> {
        let file = File::open(format!("{}{}", filename, INSTANCE_VARS_EXT))?;
        let instance_parser = var_grammar::InstanceVarParser::new();
        for line in BufReader::new(file).lines() {
            let (name, bytes) = instance_parser.parse(&line.unwrap()).unwrap();
            self.set_instance(name, bytes);
        }
        Ok(())
    }

    /// read prover commitments from .coms file
    pub fn parse_coms(&mut self, filename: String, verifier: &mut Verifier) -> std::io::Result<()> {
        let file = File::open(format!("{}{}", filename, COMMITMENTS_EXT))?;
        let commitment_parser = var_grammar::CommitmentVarParser::new();
        for line in BufReader::new(file).lines() {
            let (name, bytes) = commitment_parser.parse(&line.unwrap()).unwrap();
            let com = CompressedRistretto::from_slice(&bytes);
            self.set_commitment(name, verifier.commit(com));
        }
        Ok(())
    }

    /// commit to vars from .wtns file to .coms file
    pub fn parse_wtns(
        &mut self, 
        filename: String, 
        prover: &mut Prover,
        coms_file: &mut File
    ) -> std::io::Result<()> {
        let file = File::open(format!("{}{}", filename, WITNESS_VARS_EXT))?;
        let witness_parser = var_grammar::WitnessVarParser::new();
        for line in BufReader::new(file).lines() {
            let (name, bytes) = witness_parser.parse(&line.unwrap()).unwrap();
            let commitment = commit(prover, &bytes);
            self.witness_vars.insert(name.clone(), commitment.clone());
            for (index, com) in commitment.1.iter().enumerate() {
                coms_file.write_all(&format_com("C", &name[1..name.len()], &index, com))?;
            }
        }
        Ok(())
    }

    /// write derived witness commitment to .coms file
    pub fn parse_derived_wtns(
        &self,
        coms: Vec<CompressedRistretto>,
        gadget: usize,
        coms_file: &mut File
    ) -> std::io::Result<()> {
        for (index, com) in coms.iter().enumerate() {
            coms_file.write_all(&format_com("D", &gadget.to_string(), &index, com))?;
        }
        Ok(())
    }
}

fn format_com(
    identifier: &str, 
    gadget_no: &str, 
    com_idx: &usize, 
    com: &CompressedRistretto
) -> Vec<u8> {
    format!("{}{}-{} = 0x{}\n", identifier, gadget_no, com_idx, hex::encode(com.as_bytes())).into_bytes()
}

pub fn assert_32(name: String, assignment: &Vec<u8>) {
    assert!(assignment.len() <= 32, format!("instance var {} is longer than 32 bytes", &name));
}

pub fn assert_witness_32(
    name: String, 
    assignment: &(Vec<Scalar>, Vec<CompressedRistretto>, Vec<Variable>)
) {
    assert!(assignment.0.len() == 1, format!("witness var {} is longer than 32 bytes", &name));
}