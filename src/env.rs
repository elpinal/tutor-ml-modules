#![allow(dead_code)]

use crate::ident::*;
use crate::il::sig::*;
use crate::il::tycon::*;

use std::collections::HashMap;

use thiserror::Error;

#[derive(Clone)]
pub struct Env {
    rank: usize,
    sig: Sig,
    tv: HashMap<TypeVar, FVar>,
}

#[derive(Error, Debug)]
pub enum EnvError {
    #[error("unbound module identifier: {0}")]
    UnboundModule(ModuleIdent),
    #[error("unbound signature identifier: {0}")]
    UnboundSignature(SignatureIdent),
    #[error("unbound value identifier: {0}")]
    UnboundValue(ValueIdent),
    #[error("unbound type identifier: {0}")]
    UnboundType(TypeIdent),
    #[error("unbound type variable: {0}")]
    UnboundTypeVar(TypeVar),
}

type Result<T> = std::result::Result<T, EnvError>;

impl Env {
    pub fn initial() -> Self {
        Env {
            rank: 0,
            sig: Sig::default(),
            tv: HashMap::new(),
        }
    }

    pub fn increment_rank(&mut self) {
        self.rank += 1;
    }

    pub fn get_rank(&self) -> Rank {
        Rank::Nat(self.rank)
    }

    pub fn insert(&mut self, sig: Sig) {
        self.sig.insert(sig);
    }

    pub fn insert_type_var(&mut self, tv: TypeVar, fv: FVar) {
        self.tv.insert(tv, fv);
    }

    pub fn lookup_module(&self, id: &ModuleIdent) -> Result<Sig> {
        self.sig
            .m
            .get(id)
            .cloned()
            .ok_or_else(|| EnvError::UnboundModule(id.clone()))
    }

    pub fn lookup_signature(&self, id: &SignatureIdent) -> Result<Family> {
        self.sig
            .s
            .get(id)
            .cloned()
            .ok_or_else(|| EnvError::UnboundSignature(id.clone()))
    }

    pub fn lookup_value(&self, id: &ValueIdent) -> Result<Scheme> {
        self.sig
            .v
            .get(id)
            .cloned()
            .ok_or_else(|| EnvError::UnboundValue(id.clone()))
    }

    pub fn lookup_type(&self, id: &TypeIdent) -> Result<(Tycon, Kind)> {
        self.sig
            .t
            .get(id)
            .cloned()
            .ok_or_else(|| EnvError::UnboundType(id.clone()))
    }

    pub fn lookup_type_var(&self, id: &TypeVar) -> Result<FVar> {
        self.tv
            .get(id)
            .cloned()
            .ok_or_else(|| EnvError::UnboundTypeVar(id.clone()))
    }

    pub fn insert_value(&mut self, id: ValueIdent, x: Scheme) {
        self.sig.v.insert(id, x);
    }
}
