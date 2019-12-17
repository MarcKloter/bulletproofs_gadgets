use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier, Variable, LinearCombination, R1CSError};
use crate::curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

#[derive(Clone)]
pub enum Operation {
    Multiply((LinearCombination, LinearCombination)),
    AllocateMultiplier(Option<(Scalar, Scalar)>),
    Constrain(LinearCombination),
    Commit(Vec<Scalar>)
}

pub trait ConstraintSystemBuffer {
    /// stores the current multiply and constrain buffers in the buffer vec
    fn rewind(&mut self);

    fn buffer(&self) -> &Vec<Operation>;

    fn buffer_cache(&self) -> &Vec<Vec<Operation>>;
}

pub struct ProverBuffer<'t, 'g> {
    prover: Prover<'t, 'g>,
    operation_buffer: Vec<Operation>,
    cached_buffers: Vec<Vec<Operation>>
}

impl<'t, 'g> ProverBuffer<'t, 'g> {
    pub fn new(prover: Prover<'t, 'g>) -> ProverBuffer<'t, 'g> {
        ProverBuffer {
            prover: prover,
            operation_buffer: Vec::new(),
            cached_buffers: Vec::new()
        }
    }

    pub fn commit(&mut self, witnesses: &Vec<Scalar>) {
        for scalar in witnesses {
            self.prover.commit(*scalar, Scalar::zero());
        }
    }

    pub fn commit_drvd(&mut self, derived_witnesses: &Vec<(Option<Scalar>, Variable)>) {
        let scalars = derived_witnesses.into_iter().map(|derived| derived.0.unwrap()).collect();
        self.commit(&scalars);
        self.operation_buffer.push(Operation::Commit(scalars));
    }

    pub fn initialize_from(
        &mut self,
        initialization: Vec<Vec<Operation>>,
    ) {
        for operations in initialization {
            for operation in operations {
                match operation {
                    Operation::Multiply((left, right)) => {
                        self.prover.multiply(left.clone(), right.clone());
                    },
                    Operation::AllocateMultiplier(assignment) => { 
                        assert!(self.prover.allocate_multiplier(assignment.clone()).is_ok());
                    },
                    Operation::Constrain(lc) => {
                        self.prover.constrain(lc.clone());
                    },
                    Operation::Commit(_) => {
                        // nop
                    }
                }
            }
        }
    }
}

impl<'t, 'g> ConstraintSystemBuffer for ProverBuffer<'t, 'g> {
    fn rewind(&mut self) {
        self.cached_buffers.push(self.operation_buffer.clone());
        self.operation_buffer = Vec::new();
    }

    fn buffer(&self) -> &Vec<Operation> {
        &self.operation_buffer
    }

    fn buffer_cache(&self) -> &Vec<Vec<Operation>> {
        &self.cached_buffers
    }
}

impl<'t, 'g> ConstraintSystem for ProverBuffer<'t, 'g> {
    fn transcript(&mut self) -> &mut Transcript {
        self.prover.transcript()
    }

    fn multiply(&mut self, left: LinearCombination, right: LinearCombination) -> (Variable, Variable, Variable) {
        self.operation_buffer.push(Operation::Multiply((left.clone(), right.clone())));
        self.prover.multiply(left, right)
    }

    fn allocate(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        Err(R1CSError::GadgetError { description: "call to unimplemented method allocate".to_string() })
    }

    fn allocate_multiplier(&mut self, input_assignments: Option<(Scalar, Scalar)>) -> Result<(Variable, Variable, Variable), R1CSError> {
        let (l, r) = input_assignments.ok_or(R1CSError::MissingAssignment)?;
        self.operation_buffer.push(Operation::AllocateMultiplier(Some((l.clone(), r.clone()))));
        self.prover.allocate_multiplier(Some((l, r)))
    }
    
    fn constrain(&mut self, lc: LinearCombination) {
        self.operation_buffer.push(Operation::Constrain(lc.clone()));
        self.prover.constrain(lc);
    }
}

pub struct VerifierBuffer<'t> {
    verifier: Verifier<'t>,
    operation_buffer: Vec<Operation>,
    cached_buffers: Vec<Vec<Operation>>
}

impl<'t> VerifierBuffer<'t> {
    pub fn new(verifier: Verifier<'t>) -> VerifierBuffer<'t> {
        VerifierBuffer {
            verifier: verifier,
            operation_buffer: Vec::new(),
            cached_buffers: Vec::new()
        }
    }

    pub fn initialize_from(
        &mut self,
        initialization: Vec<Vec<Operation>>,
    ) {
        for operations in initialization {
            for operation in operations {
                match operation {
                    Operation::Multiply((left, right)) => {
                        self.verifier.multiply(left.clone(), right.clone());
                    },
                    Operation::AllocateMultiplier(assignment) => { 
                        assert!(self.verifier.allocate_multiplier(assignment.clone()).is_ok());
                    },
                    Operation::Constrain(lc) => {
                        self.verifier.constrain(lc.clone());
                    },
                    Operation::Commit(_) => {
                        // nop
                    }
                }
            }
        }
    }
}

impl<'t> ConstraintSystemBuffer for VerifierBuffer<'t> {    
    fn rewind(&mut self) {
        self.cached_buffers.push(self.operation_buffer.clone());
        self.operation_buffer = Vec::new();
    }

    fn buffer(&self) -> &Vec<Operation> {
        &self.operation_buffer
    }

    fn buffer_cache(&self) -> &Vec<Vec<Operation>> {
        &self.cached_buffers
    }
}

impl<'t> ConstraintSystem for VerifierBuffer<'t> {
    fn transcript(&mut self) -> &mut Transcript {
        self.verifier.transcript()
    }

    fn multiply(&mut self, left: LinearCombination, right: LinearCombination) -> (Variable, Variable, Variable) {
        self.operation_buffer.push(Operation::Multiply((left.clone(), right.clone())));
        self.verifier.multiply(left, right)
    }

    fn allocate(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        Err(R1CSError::GadgetError { description: "call to unimplemented method allocate".to_string() })
    }

    fn allocate_multiplier(&mut self, _: Option<(Scalar, Scalar)>) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.operation_buffer.push(Operation::AllocateMultiplier(None));
        self.verifier.allocate_multiplier(None)
    }
    
    fn constrain(&mut self, lc: LinearCombination) {
        self.operation_buffer.push(Operation::Constrain(lc.clone()));
        self.verifier.constrain(lc);
    }
}