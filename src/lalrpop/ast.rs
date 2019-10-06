use std::str::FromStr;

pub enum GadgetOp {
    Hash,
    Bound,
    Merkle,
    Equality
}

#[derive(Clone)]
pub enum Var {
    Instance(String),
    Witness(String),
    Commitment(String),
    Derived(String)
}

impl GadgetOp {
    pub fn as_str(&self) -> &'static str {
        match self {
            GadgetOp::Hash => "HASH",
            GadgetOp::Bound => "BOUND",
            GadgetOp::Merkle => "MERKLE",
            GadgetOp::Equality => "EQUALS"
        }
    }
}

impl FromStr for GadgetOp {
    type Err = ();
    
    fn from_str(s: &str) -> Result<GadgetOp, ()> {
        match s {
            "HASH" => Ok(GadgetOp::Hash),
            "BOUND" => Ok(GadgetOp::Bound),
            "MERKLE" => Ok(GadgetOp::Merkle),
            "EQUALS" => Ok(GadgetOp::Equality),
            _ => Err(()),
        }
    }
}