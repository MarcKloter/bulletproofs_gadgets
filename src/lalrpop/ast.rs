use std::str::FromStr;

pub enum GadgetOp {
    Hash,
    Bound,
    Merkle,
    Equality,
    Inequality,
    SetMembership
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
            GadgetOp::Equality => "EQUALS",
            GadgetOp::Inequality => "UNEQUAL",
            GadgetOp::SetMembership => "SET_MEMBER"
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
            "UNEQUAL" => Ok(GadgetOp::Inequality),
            "SET_MEMBER" => Ok(GadgetOp::SetMembership),
            _ => Err(()),
        }
    }
}