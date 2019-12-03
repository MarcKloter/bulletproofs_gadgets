use std::str::FromStr;

pub enum GadgetOp {
    Or,
    Hash,
    Bound,
    Merkle,
    LessThan,
    ArrayEnd,
    Equality,
    ArrayStart,
    Inequality,
    CodeBlockEnd,
    SetMembership,
    CodeBlockStart,
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
            GadgetOp::Or => "OR",
            GadgetOp::Hash => "HASH",
            GadgetOp::ArrayEnd => "]",
            GadgetOp::Bound => "BOUND",
            GadgetOp::ArrayStart => "[",
            GadgetOp::Merkle => "MERKLE",
            GadgetOp::CodeBlockEnd => "}",
            GadgetOp::Equality => "EQUALS",
            GadgetOp::CodeBlockStart => "{",
            GadgetOp::LessThan => "LESS_THAN",
            GadgetOp::Inequality => "UNEQUAL",
            GadgetOp::SetMembership => "SET_MEMBER"
        }
    }

    pub fn is_block_end(&self) -> bool {
        match *self {
            GadgetOp::CodeBlockEnd => true,
            _ => false,
        }
    }

    pub fn is_array_start(&self) -> bool {
        match *self {
            GadgetOp::ArrayStart => true,
            _ => false,
        }
    }

    pub fn is_array_end(&self) -> bool {
        match *self {
            GadgetOp::ArrayEnd => true,
            _ => false,
        }
    }
}

impl FromStr for GadgetOp {
    type Err = ();
    
    fn from_str(s: &str) -> Result<GadgetOp, ()> {
        match s {
            "OR" => Ok(GadgetOp::Or),
            "HASH" => Ok(GadgetOp::Hash),
            "]" => Ok(GadgetOp::ArrayEnd),
            "BOUND" => Ok(GadgetOp::Bound),
            "[" => Ok(GadgetOp::ArrayStart),
            "MERKLE" => Ok(GadgetOp::Merkle),
            "}" => Ok(GadgetOp::CodeBlockEnd),
            "EQUALS" => Ok(GadgetOp::Equality),
            "{" => Ok(GadgetOp::CodeBlockStart),
            "UNEQUAL" => Ok(GadgetOp::Inequality),
            "LESS_THAN" => Ok(GadgetOp::LessThan),
            "SET_MEMBER" => Ok(GadgetOp::SetMembership),
            _ => Err(()),
        }
    }
}