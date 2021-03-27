use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleIdent(String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SignatureIdent(String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueIdent(String);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeIdent(String);

#[derive(Clone, Debug)]
pub struct Loc<T>(pub Vec<ModuleIdent>, pub T);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeVar(String);

impl From<String> for ModuleIdent {
    fn from(s: String) -> Self {
        ModuleIdent(s)
    }
}

impl fmt::Display for ModuleIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl From<String> for SignatureIdent {
    fn from(s: String) -> Self {
        SignatureIdent(s)
    }
}

impl fmt::Display for SignatureIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl From<String> for ValueIdent {
    fn from(s: String) -> Self {
        ValueIdent(s)
    }
}

impl fmt::Display for ValueIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl From<String> for TypeIdent {
    fn from(s: String) -> Self {
        TypeIdent(s)
    }
}

impl fmt::Display for TypeIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::Display> fmt::Display for Loc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for x in self.0.iter() {
            x.fmt(f)?;
            write!(f, ".")?;
        }
        self.1.fmt(f)
    }
}

impl From<String> for TypeVar {
    fn from(s: String) -> Self {
        TypeVar(s)
    }
}

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}
