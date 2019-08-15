use std::str::FromStr;

pub enum GadgetOp {
    Hash,
    Bound,
    Merkle
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
            GadgetOp::Merkle => "MERKLE"
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
            _ => Err(()),
        }
    }
}