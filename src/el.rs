pub use crate::ident::*;
pub use crate::kind::Kind;

use std::collections::HashSet;

#[derive(Debug)]
pub enum Module {
    Ident(ModuleIdent),
    Seq(Vec<Binding>),
    Proj(Box<Module>, ModuleIdent),
    Curtail(Box<Module>, Signature),
    Seal(Box<Module>, Signature),
}

#[derive(Debug)]
pub enum Binding {
    Module(ModuleIdent, Module),
    Signature(SignatureIdent, Signature),
    Value(ValueIdent, Expr),
    Type(TypeIdent, Tycon),
    Include(Module),
}

#[derive(Debug)]
pub enum Signature {
    Ident(SignatureIdent),
    Seq(Vec<Decl>),
    Proj(Box<Module>, SignatureIdent),
    WhereType(Box<Signature>, Loc<TypeIdent>, Tycon),
}

#[derive(Debug)]
pub enum Decl {
    Module(ModuleIdent, Signature),
    Signature(SignatureIdent, Signature),
    Value(ValueIdent, Scheme),
    TypeTrans(TypeIdent, Tycon),
    Type(TypeIdent, Kind),
    Include(Signature),
}

#[derive(Debug)]
pub enum Expr {
    Ident(ValueIdent),
    Proj(Box<Module>, ValueIdent),
    Abs(ValueIdent, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum Tycon {
    Ident(TypeIdent),
    Proj(Box<Module>, TypeIdent),
    Var(TypeVar),
    Abs(TypeVar, Box<Tycon>),
    App(Box<Tycon>, Box<Tycon>),
    Arrow(Box<Tycon>, Box<Tycon>),
}

#[derive(Debug)]
pub enum Scheme {
    Forall(TypeVar, Box<Scheme>),
    Body(Tycon),
}

fn check_duplicates(tvs: &[TypeVar]) -> Result<(), &'static str> {
    let mut set = HashSet::new();
    for tv in tvs {
        if !set.insert(tv) {
            return Err("duplicate type variables!");
        }
    }
    Ok(())
}

impl Decl {
    pub fn value(id: ValueIdent, tvs: Vec<TypeVar>, ty: Tycon) -> Result<Self, &'static str> {
        check_duplicates(&tvs)?;

        let scheme = tvs.into_iter().rfold(Scheme::Body(ty), |acc, tv| {
            Scheme::Forall(tv, Box::new(acc))
        });
        Ok(Decl::Value(id, scheme))
    }

    pub fn r#type(
        id: TypeIdent,
        tvs: Vec<TypeVar>,
        ty1: Option<Tycon>,
    ) -> Result<Self, &'static str> {
        check_duplicates(&tvs)?;

        if let Some(ty1) = ty1 {
            let ty = tvs
                .into_iter()
                .rfold(ty1, |acc, tv| Tycon::Abs(tv, Box::new(acc)));
            Ok(Decl::TypeTrans(id, ty))
        } else {
            let k = tvs.into_iter().rfold(Kind::Base, |acc, _| Kind::arrow(acc));
            Ok(Decl::Type(id, k))
        }
    }
}

impl Tycon {
    pub fn abs(tvs: Vec<TypeVar>, ty1: Tycon) -> Result<Self, &'static str> {
        check_duplicates(&tvs)?;

        let ty = tvs
            .into_iter()
            .rfold(ty1, |acc, tv| Tycon::Abs(tv, Box::new(acc)));
        Ok(ty)
    }
}

impl From<Tycon> for Scheme {
    fn from(ty: Tycon) -> Self {
        Scheme::Body(ty)
    }
}
