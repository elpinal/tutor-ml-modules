#![allow(dead_code)]

use super::tycon::*;
use crate::ident::*;

use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::fmt;

use thiserror::Error;

#[derive(Clone, Debug, Default)]
pub struct Sig {
    pub m: BTreeMap<ModuleIdent, Sig>,
    pub s: BTreeMap<SignatureIdent, Family>,
    pub v: BTreeMap<ValueIdent, Scheme>,
    pub t: BTreeMap<TypeIdent, (Tycon, Kind)>,
}

#[derive(Clone, Debug)]
pub struct Family {
    vars: Vec<(Kind, Loc<TypeIdent>)>,
    body: Sig,
}

#[derive(Clone, Debug)]
pub struct ExSig {
    vars: Vec<Kind>,
    body: Sig,
}

#[derive(Clone, Debug)]
pub struct Scheme {
    vars: usize,
    body: Atom,
}

#[derive(Error, Debug)]
pub enum SigError {
    #[error("no such module component: {0}")]
    NoSuchModule(ModuleIdent),
    #[error("no such signature component: {0}")]
    NoSuchSignature(SignatureIdent),
    #[error("no such value component: {0}")]
    NoSuchValue(ValueIdent),
    #[error("no such type component: {0}")]
    NoSuchType(TypeIdent),

    #[error("no such module component: {0}")]
    NoSuchModuleLoc(Loc<ModuleIdent>),
    #[error("no such type component: {0}")]
    NoSuchTypeLoc(Loc<TypeIdent>),

    #[error("duplicate module component: {0}")]
    DuplicateModule(ModuleIdent),
    #[error("duplicate signature component: {0}")]
    DuplicateSignature(SignatureIdent),
    #[error("duplicate value component: {0}")]
    DuplicateValue(ValueIdent),
    #[error("duplicate type component: {0}")]
    DuplicateType(TypeIdent),
}

impl DisplayTable for Sig {
    fn fmt_with_table(&self, f: &mut fmt::Formatter, table: &mut UnifTable) -> fmt::Result {
        write!(f, "{{")?;
        self.m.iter().try_for_each(|(id, x)| {
            write!(f, "{} : ", id)?;
            x.fmt_with_table(f, table)?;
            write!(f, ", ")
        })?;
        self.s.iter().try_for_each(|(id, x)| {
            write!(f, "{} = ", id)?;
            x.fmt_with_table(f, table)?;
            write!(f, ", ")
        })?;
        self.v.iter().try_for_each(|(id, x)| {
            write!(f, "{} : ", id)?;
            x.fmt_with_table(f, table)?;
            write!(f, ", ")
        })?;
        self.t.iter().try_for_each(|(id, (ty, k))| {
            write!(f, "{} = ", id)?;
            ty.fmt_with_table(f, table)?;
            write!(f, " : {}, ", k)
        })?;
        write!(f, "}}")?;
        Ok(())
    }
}

impl Find for (Tycon, Kind) {
    fn find_bound(&self, table: &UnifTable, j: usize) -> Result<(), anyhow::Error> {
        self.0.find_bound(table, j)
    }
}

impl Find for Sig {
    fn find_bound(&self, table: &UnifTable, j: usize) -> Result<(), anyhow::Error> {
        self.m
            .values()
            .try_for_each(|sig| sig.find_bound(table, j))?;
        self.s
            .values()
            .try_for_each(|fsig| fsig.find_bound(table, j))?;
        self.v
            .values()
            .try_for_each(|scheme| scheme.find_bound(table, j))?;
        self.t
            .values()
            .try_for_each(|tyk| tyk.find_bound(table, j))?;
        Ok(())
    }
}

impl Close for Sig {
    fn close(&mut self, table: &UnifTable, j: usize, fvs: &[FVar]) {
        self.m.values_mut().for_each(|sig| sig.close(table, j, fvs));
        self.s
            .values_mut()
            .for_each(|fsig| fsig.close(table, j, fvs));
        self.v
            .values_mut()
            .for_each(|scheme| scheme.close(table, j, fvs));
        self.t
            .values_mut()
            .for_each(|(ty, _)| ty.close(table, j, fvs));
    }
}

impl Open for Sig {
    fn open(&mut self, table: &UnifTable, j: usize, tys: &[Tycon]) {
        self.m.values_mut().for_each(|sig| sig.open(table, j, tys));
        self.s
            .values_mut()
            .for_each(|fsig| fsig.open(table, j, tys));
        self.v
            .values_mut()
            .for_each(|scheme| scheme.open(table, j, tys));
        self.t
            .values_mut()
            .for_each(|(ty, _)| ty.open(table, j, tys));
    }
}

fn insert_or_err<K: Ord, V, F>(entry: Entry<K, V>, x: V, f: F) -> Result<(), SigError>
where
    F: FnOnce(K) -> SigError,
{
    match entry {
        Entry::Occupied(e) => Err(f(e.remove_entry().0)),
        Entry::Vacant(e) => {
            e.insert(x);
            Ok(())
        }
    }
}

impl Sig {
    pub fn get_module_identifiers(&self) -> impl Iterator<Item = &ModuleIdent> {
        self.m.keys()
    }

    pub fn get_value_identifiers(&self) -> impl Iterator<Item = &ValueIdent> {
        self.v.keys()
    }

    pub fn singleton_module(id: ModuleIdent, x: Sig) -> Self {
        Sig {
            m: vec![(id, x)].into_iter().collect(),
            ..Sig::default()
        }
    }

    pub fn singleton_signature(id: SignatureIdent, x: Family) -> Self {
        Sig {
            s: vec![(id, x)].into_iter().collect(),
            ..Sig::default()
        }
    }

    pub fn singleton_value(id: ValueIdent, x: Scheme) -> Self {
        Sig {
            v: vec![(id, x)].into_iter().collect(),
            ..Sig::default()
        }
    }

    pub fn singleton_type(id: TypeIdent, x: (Tycon, Kind)) -> Self {
        Sig {
            t: vec![(id, x)].into_iter().collect(),
            ..Sig::default()
        }
    }

    pub fn insert(&mut self, sig: Sig) {
        self.m.extend(sig.m);
        self.s.extend(sig.s);
        self.v.extend(sig.v);
        self.t.extend(sig.t);
    }

    pub fn insert_disjoint(&mut self, sig: Sig) -> Result<(), SigError> {
        use SigError::*;
        sig.m
            .into_iter()
            .try_for_each(|(id, x)| insert_or_err(self.m.entry(id), x, DuplicateModule))?;
        sig.s
            .into_iter()
            .try_for_each(|(id, x)| insert_or_err(self.s.entry(id), x, DuplicateSignature))?;
        sig.v
            .into_iter()
            .try_for_each(|(id, x)| insert_or_err(self.v.entry(id), x, DuplicateValue))?;
        sig.t
            .into_iter()
            .try_for_each(|(id, x)| insert_or_err(self.t.entry(id), x, DuplicateType))?;
        Ok(())
    }

    pub fn subst(&mut self, table: &UnifTable, fv: FVar, ty: Tycon) {
        self.close(table, 0, &[fv]);
        self.open(table, 0, &[ty]);
    }

    pub fn proj_module(&self, id: &ModuleIdent) -> Result<Sig, SigError> {
        self.m
            .get(id)
            .cloned()
            .ok_or_else(|| SigError::NoSuchModule(id.clone()))
    }

    pub fn proj_signature(&self, id: &SignatureIdent) -> Result<Family, SigError> {
        self.s
            .get(id)
            .cloned()
            .ok_or_else(|| SigError::NoSuchSignature(id.clone()))
    }

    pub fn proj_value(&self, id: &ValueIdent) -> Result<Scheme, SigError> {
        self.v
            .get(id)
            .cloned()
            .ok_or_else(|| SigError::NoSuchValue(id.clone()))
    }

    pub fn proj_type(&self, id: &TypeIdent) -> Result<(Tycon, Kind), SigError> {
        self.t
            .get(id)
            .cloned()
            .ok_or_else(|| SigError::NoSuchType(id.clone()))
    }

    pub fn proj_type_loc(&self, loc: &Loc<TypeIdent>) -> Result<(Tycon, Kind), SigError> {
        let Loc(mids, tid) = loc;
        let mut sig = self;
        for (i, mid) in mids.iter().enumerate() {
            if let Some(x) = sig.m.get(mid) {
                sig = x;
            } else {
                return Err(SigError::NoSuchModuleLoc(Loc(
                    mids[..i].to_vec(),
                    mid.clone(),
                )));
            }
        }
        sig.t
            .get(tid)
            .cloned()
            .ok_or_else(|| SigError::NoSuchTypeLoc(loc.clone()))
    }

    pub fn is_subtype_of(&self, table: &mut UnifTable, against: &Sig) -> anyhow::Result<()> {
        against
            .m
            .iter()
            .try_for_each(|(id, sig)| self.proj_module(id)?.is_subtype_of(table, sig))?;
        against
            .s
            .iter()
            .try_for_each(|(id, fsig)| self.proj_signature(id)?.equiv(table, fsig))?;
        against
            .v
            .iter()
            .try_for_each(|(id, scheme)| self.proj_value(id)?.is_general_than(table, scheme))?;
        against.t.iter().try_for_each(|(id, (ty2, k2))| {
            let (ty1, k1) = self.proj_type(id)?;
            k1.unify(k2)?;
            ty1.unify(table, ty2)
        })?;
        Ok(())
    }

    pub fn r#match(&self, table: &mut UnifTable, against: &Family) -> anyhow::Result<Vec<Tycon>> {
        let mut tys = Vec::new();
        for (k, loc) in &against.vars {
            let (ty1, k1) = self.proj_type_loc(loc)?;
            k1.unify(k)?;
            tys.push(ty1);
        }

        let mut sig = against.body.clone();
        sig.open(table, 0, &tys);
        self.is_subtype_of(table, &sig)?;

        Ok(tys)
    }
}

impl DisplayTable for Family {
    fn fmt_with_table(&self, f: &mut fmt::Formatter, table: &mut UnifTable) -> fmt::Result {
        if self.vars.is_empty() {
            return self.body.fmt_with_table(f, table);
        }

        let (xs, sig) = self.clone().get_body(table);
        write!(
            f,
            "λ{} => ",
            FVars(xs.into_iter().map(|(fv, _)| fv).collect())
        )?;
        sig.fmt_with_table(f, table)?;
        Ok(())
    }
}

impl Find for Family {
    fn find_bound(&self, table: &UnifTable, j: usize) -> Result<(), anyhow::Error> {
        self.body.find_bound(table, j + 1)
    }
}

impl Close for Family {
    fn close(&mut self, table: &UnifTable, j: usize, fvs: &[FVar]) {
        self.body.close(table, j + 1, fvs);
    }
}

impl Open for Family {
    fn open(&mut self, table: &UnifTable, j: usize, tys: &[Tycon]) {
        self.body.open(table, j + 1, tys);
    }
}

impl From<Sig> for Family {
    fn from(s: Sig) -> Self {
        Family {
            vars: Vec::new(),
            body: s,
        }
    }
}

impl Family {
    pub fn map<F, G>(self, mut f: F, g: G) -> Self
    where
        F: FnMut(Loc<TypeIdent>) -> Loc<TypeIdent>,
        G: FnOnce(Sig) -> Sig,
    {
        Family {
            vars: self.vars.into_iter().map(|(k, loc)| (k, f(loc))).collect(),
            body: g(self.body),
        }
    }

    pub fn get_body(self, table: &mut UnifTable) -> (Vec<(FVar, Loc<TypeIdent>)>, Sig) {
        let xs: Vec<_> = self
            .vars
            .into_iter()
            .map(|(k, loc)| (table.fresh_fvar(k), loc))
            .collect();

        let mut body = self.body;
        body.open(
            table,
            0,
            &xs.iter()
                .map(|(fv, _)| Tycon::Body(Atom::Free(fv.clone())))
                .collect::<Vec<_>>(),
        );
        (xs, body)
    }

    pub fn quantify(table: &UnifTable, xs: Vec<(FVar, Loc<TypeIdent>)>, mut sig: Sig) -> Self {
        let fvs: Vec<_> = xs.iter().map(|(fv, _)| fv.clone()).collect();
        sig.close(table, 0, &fvs);

        let ys = xs
            .into_iter()
            .map(|(fv, loc)| (fv.get_kind(), loc))
            .collect();
        Family {
            vars: ys,
            body: sig,
        }
    }

    pub fn is_subtype_of(&self, table: &mut UnifTable, against: &Family) -> anyhow::Result<()> {
        let (_, sig) = self.clone().get_body(table);
        let _ = sig.r#match(table, against)?;
        Ok(())
    }

    pub fn equiv(&self, table: &mut UnifTable, against: &Family) -> anyhow::Result<()> {
        self.is_subtype_of(table, against)?;
        against.is_subtype_of(table, self)?;
        Ok(())
    }

    pub fn instantiate(self, table: &UnifTable, tys: &[Tycon]) -> Sig {
        let mut sig = self.body;
        sig.open(table, 0, tys);
        sig
    }
}

impl DisplayTable for ExSig {
    fn fmt_with_table(&self, f: &mut fmt::Formatter, table: &mut UnifTable) -> fmt::Result {
        if self.vars.is_empty() {
            return self.body.fmt_with_table(f, table);
        }

        let (fvs, sig) = self.clone().get_body(table);
        write!(f, "∃{}. ", FVars(fvs))?;
        sig.fmt_with_table(f, table)?;
        Ok(())
    }
}

impl From<Sig> for ExSig {
    fn from(s: Sig) -> Self {
        ExSig {
            vars: Vec::new(),
            body: s,
        }
    }
}

impl From<Family> for ExSig {
    fn from(fsig: Family) -> Self {
        ExSig {
            vars: fsig.vars.into_iter().map(|(k, _)| k).collect(),
            body: fsig.body,
        }
    }
}

impl ExSig {
    pub fn map<F>(self, f: F) -> Self
    where
        F: FnOnce(Sig) -> Sig,
    {
        ExSig {
            body: f(self.body),
            ..self
        }
    }

    pub fn try_map<E, F>(self, f: F) -> Result<Self, E>
    where
        F: FnOnce(Sig) -> Result<Sig, E>,
    {
        Ok(ExSig {
            body: f(self.body)?,
            ..self
        })
    }

    pub fn escape<I, F>(self, table: &UnifTable, f: F) -> anyhow::Result<I>
    where
        I: Find,
        F: FnOnce(Sig) -> anyhow::Result<I>,
    {
        let i = f(self.body)?;
        i.find_bound(table, 0)?;
        Ok(i)
    }

    pub fn get_body(self, table: &mut UnifTable) -> (Vec<FVar>, Sig) {
        let xs: Vec<_> = self.vars.into_iter().map(|k| table.fresh_fvar(k)).collect();

        let mut body = self.body;
        body.open(
            table,
            0,
            &xs.iter()
                .map(|fv| Tycon::Body(Atom::Free(fv.clone())))
                .collect::<Vec<_>>(),
        );
        (xs, body)
    }

    pub fn quantify(table: &UnifTable, fvs: Vec<FVar>, mut sig: Sig) -> Self {
        sig.close(table, 0, &fvs);

        let ks = fvs.into_iter().map(|fv| fv.get_kind()).collect();
        ExSig {
            vars: ks,
            body: sig,
        }
    }

    pub fn get_module_identifiers(&self) -> impl Iterator<Item = &ModuleIdent> {
        self.body.m.keys()
    }

    pub fn get_value_identifiers(&self) -> impl Iterator<Item = &ValueIdent> {
        self.body.v.keys()
    }
}

impl DisplayTable for Scheme {
    fn fmt_with_table(&self, f: &mut fmt::Formatter, table: &mut UnifTable) -> fmt::Result {
        if self.vars == 0 {
            return write!(f, "{}", self.body);
        }

        let n = self.vars;
        let fvs: Vec<_> = (0..n).map(|_| table.fresh_fvar(Kind::Base)).collect();
        let mut a = self.body.clone();
        a.open_as_atom(
            table,
            0,
            &fvs.iter()
                .map(|fv| Tycon::fvar(fv.clone()))
                .collect::<Vec<_>>(),
        );

        write!(f, "∀{}. {}", FVars(fvs), a)?;
        Ok(())
    }
}

impl Find for Scheme {
    fn find_bound(&self, table: &UnifTable, j: usize) -> Result<(), anyhow::Error> {
        self.body.find_bound(table, j + 1)
    }
}

impl Close for Scheme {
    fn close(&mut self, table: &UnifTable, j: usize, fvs: &[FVar]) {
        self.body.close(table, j + 1, fvs);
    }
}

impl Open for Scheme {
    fn open(&mut self, table: &UnifTable, j: usize, tys: &[Tycon]) {
        self.body.open_as_atom(table, j + 1, tys);
    }
}

impl From<Atom> for Scheme {
    fn from(body: Atom) -> Self {
        Scheme { vars: 0, body }
    }
}

impl Scheme {
    pub fn instantiate(self, table: &mut UnifTable) -> Atom {
        let n = self.vars;
        let uvs: Vec<_> = (0..n)
            .map(|_| table.fresh_uvar(Rank::Infinity))
            .map(Atom::Unif)
            .map(Tycon::Body)
            .collect();

        let mut a = self.body;
        a.open_as_atom(table, 0, &uvs);
        a
    }

    pub fn is_general_than(&self, table: &mut UnifTable, scheme: &Scheme) -> anyhow::Result<()> {
        let a1 = self.clone().instantiate(table);

        let n = scheme.vars;
        let fvs: Vec<_> = (0..n)
            .map(|_| table.fresh_fvar(Kind::Base))
            .map(Atom::Free)
            .map(Tycon::Body)
            .collect();

        let mut a2 = scheme.body.clone();
        a2.open_as_atom(table, 0, &fvs);

        a1.unify(table, &a2)
    }

    pub fn generalize(table: &mut UnifTable, rank: Rank, mut a: Atom) -> Self {
        let mut fvs = Vec::new();
        a.replace_uvars(table, rank, &mut fvs);
        a.close(table, 0, &fvs);
        Scheme {
            vars: fvs.len(),
            body: a,
        }
    }

    pub fn quantify(table: &UnifTable, fvs: Vec<FVar>, mut a: Atom) -> Self {
        a.close(table, 0, &fvs);
        Scheme {
            vars: fvs.len(),
            body: a,
        }
    }
}
