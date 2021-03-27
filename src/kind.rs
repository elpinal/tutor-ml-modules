use std::fmt;

use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    Base,
    Arrow(Box<Kind>),
}

#[derive(Error, Debug)]
#[error("kind mismatch: {0} vs {1}")]
pub struct KindMismatch(Kind, Kind);

impl From<&Kind> for usize {
    fn from(k: &Kind) -> Self {
        match *k {
            Kind::Base => 0,
            Kind::Arrow(ref k) => 1 + usize::from(&**k),
        }
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Kind::*;
        match self {
            Base => write!(f, "Type"),
            Arrow(x) => write!(f, "Type -> {}", x),
        }
    }
}

impl Kind {
    pub fn arrow(k: Kind) -> Self {
        Kind::Arrow(Box::new(k))
    }

    pub fn unify(&self, k: &Kind) -> Result<(), KindMismatch> {
        if self == k {
            Ok(())
        } else {
            Err(KindMismatch(self.clone(), k.clone()))
        }
    }
}
