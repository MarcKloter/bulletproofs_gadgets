use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier, Variable, LinearCombination, R1CSError};
use crate::curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

pub trait ConstraintSystemBuffer {
    fn multiplications(&self) -> &Vec<(LinearCombination, LinearCombination)>;

    fn constraints(&self) -> &Vec<LinearCombination>;

    /// stores the current multiply and constrain buffer in the buffer vec
    fn rewind(&mut self);

    fn buffer(&self) -> &Vec<(
        Vec<(LinearCombination, LinearCombination)>,
        Vec<Option<(Scalar, Scalar)>>,
        Vec<LinearCombination>
    )>;
}

pub struct ProverBuffer<'t, 'g> {
    prover: Prover<'t, 'g>,
    multiply_buffer: Vec<(LinearCombination, LinearCombination)>,
    multiply_allocation_buffer: Vec<Option<(Scalar, Scalar)>>,
    constrain_buffer: Vec<LinearCombination>,
    cached_buffers: Vec<(
        Vec<(LinearCombination, LinearCombination)>, 
        Vec<Option<(Scalar, Scalar)>>, 
        Vec<LinearCombination>
    )>
}

impl<'t, 'g> ProverBuffer<'t, 'g> {
    pub fn new(prover: Prover<'t, 'g>) -> ProverBuffer<'t, 'g> {
        ProverBuffer {
            prover: prover,
            multiply_buffer: Vec::new(),
            multiply_allocation_buffer: Vec::new(),
            constrain_buffer: Vec::new(),
            cached_buffers: Vec::new()
        }
    }

    pub fn commit(&mut self, witnesses: &Vec<Scalar>) {
        for scalar in witnesses {
            self.prover.commit(*scalar, Scalar::zero());
        }
    }

    pub fn commit_drvd(&mut self, derived_witnesses: &Vec<(Option<Scalar>, Variable)>) {
        self.commit(&derived_witnesses.into_iter().map(|derived| derived.0.unwrap()).collect());
    }
}

impl<'t, 'g> ConstraintSystemBuffer for ProverBuffer<'t, 'g> {
    fn multiplications(&self) -> &Vec<(LinearCombination, LinearCombination)> {
        &self.multiply_buffer
    }

    fn constraints(&self) -> &Vec<LinearCombination> {
        &self.constrain_buffer
    }
    
    fn rewind(&mut self) {
        self.cached_buffers.push((
            self.multiply_buffer.clone(), 
            self.multiply_allocation_buffer.clone(), 
            self.constrain_buffer.clone()
        ));
        self.multiply_buffer = Vec::new();
        self.constrain_buffer = Vec::new();
    }

    fn buffer(&self) -> &Vec<(
        Vec<(LinearCombination, LinearCombination)>, 
        Vec<Option<(Scalar, Scalar)>>, 
        Vec<LinearCombination>
    )> {
        &self.cached_buffers
    }
}

impl<'t, 'g> ConstraintSystem for ProverBuffer<'t, 'g> {
    fn transcript(&mut self) -> &mut Transcript {
        self.prover.transcript()
    }

    fn multiply(&mut self, left: LinearCombination, right: LinearCombination) -> (Variable, Variable, Variable) {
        self.multiply_buffer.push((left.clone(), right.clone()));
        self.prover.multiply(left, right)
    }

    fn allocate(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        Err(R1CSError::GadgetError { description: "call to unimplemented method allocate".to_string() })
    }

    fn allocate_multiplier(&mut self, input_assignments: Option<(Scalar, Scalar)>) -> Result<(Variable, Variable, Variable), R1CSError> {
        let (l, r) = input_assignments.ok_or(R1CSError::MissingAssignment)?;
        self.multiply_allocation_buffer.push(Some((l.clone(), r.clone())));
        self.prover.allocate_multiplier(Some((l, r)))
    }
    
    fn constrain(&mut self, lc: LinearCombination) {
        self.constrain_buffer.push(lc.clone());
        self.prover.constrain(lc);
    }
}

pub struct VerifierBuffer<'t> {
    verifier: Verifier<'t>,
    multiply_buffer: Vec<(LinearCombination, LinearCombination)>,
    multiply_allocation_buffer: Vec<Option<(Scalar, Scalar)>>,
    constrain_buffer: Vec<LinearCombination>,
    cached_buffers: Vec<(
        Vec<(LinearCombination, LinearCombination)>, 
        Vec<Option<(Scalar, Scalar)>>,
        Vec<LinearCombination>)
    >
}

impl<'t> VerifierBuffer<'t> {
    pub fn new(verifier: Verifier<'t>) -> VerifierBuffer<'t> {
        VerifierBuffer {
            verifier: verifier,
            multiply_buffer: Vec::new(),
            multiply_allocation_buffer: Vec::new(),
            constrain_buffer: Vec::new(),
            cached_buffers: Vec::new()
        }
    }
}

impl<'t> ConstraintSystemBuffer for VerifierBuffer<'t> {
    fn multiplications(&self) -> &Vec<(LinearCombination, LinearCombination)> {
        &self.multiply_buffer
    }

    fn constraints(&self) -> &Vec<LinearCombination> {
        &self.constrain_buffer
    }
    
    fn rewind(&mut self) {
        self.cached_buffers.push((
            self.multiply_buffer.clone(), 
            self.multiply_allocation_buffer.clone(), 
            self.constrain_buffer.clone()
        ));
        self.multiply_buffer = Vec::new();
        self.constrain_buffer = Vec::new();
    }

    fn buffer(&self) -> &Vec<(
        Vec<(LinearCombination, LinearCombination)>, 
        Vec<Option<(Scalar, Scalar)>>,
        Vec<LinearCombination>
    )> {
        &self.cached_buffers
    }
}

impl<'t> ConstraintSystem for VerifierBuffer<'t> {
    fn transcript(&mut self) -> &mut Transcript {
        self.verifier.transcript()
    }

    fn multiply(&mut self, left: LinearCombination, right: LinearCombination) -> (Variable, Variable, Variable) {
        self.multiply_buffer.push((left.clone(), right.clone()));
        self.verifier.multiply(left, right)
    }

    fn allocate(&mut self, _: Option<Scalar>) -> Result<Variable, R1CSError> {
        Err(R1CSError::GadgetError { description: "call to unimplemented method allocate".to_string() })
    }

    fn allocate_multiplier(&mut self, _: Option<(Scalar, Scalar)>) -> Result<(Variable, Variable, Variable), R1CSError> {
        self.multiply_allocation_buffer.push(None);
        self.verifier.allocate_multiplier(None)
    }
    
    fn constrain(&mut self, lc: LinearCombination) {
        self.constrain_buffer.push(lc.clone());
        self.verifier.constrain(lc);
    }
}