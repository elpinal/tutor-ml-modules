use crate::el;
use crate::env::Env;
use crate::ident::Loc;
use crate::il::expr;
use crate::il::sig::*;
use crate::il::tycon::*;

use anyhow::Result;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ElaborateError {
    #[error("refining a type defined outside the signature: {0}")]
    RefiningOuterType(el::Loc<el::TypeIdent>, Sig),
}

pub trait Elaborate {
    type Output;

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output>;
}

impl Elaborate for el::Module {
    type Output = (ExSig, expr::Expr);

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output> {
        match self {
            el::Module::Ident(id) => Ok((
                ExSig::from(env.lookup_module(&id)?),
                expr::Expr::module_var(id),
            )),
            el::Module::Seq(bs) => {
                let mut env = env.clone();
                let mut v: Vec<expr::Binding> = Vec::new();
                let mut whole_fvs = Vec::new();
                let mut whole_sig = Sig::default();
                for b in bs {
                    let (exsig, b) = b.elaborate(&env, table)?;
                    v.extend(b);

                    let (fvs, sig) = exsig.get_body(table);
                    whole_fvs.extend(fvs);
                    whole_sig.insert(sig.clone());
                    env.insert(sig);
                }

                let mids = whole_sig.get_module_identifiers().map(|id| {
                    (
                        expr::Label::Module(id.clone()),
                        expr::Expr::module_var(id.clone()),
                    )
                });
                let vids = whole_sig.get_value_identifiers().map(|id| {
                    (
                        expr::Label::Value(id.clone()),
                        expr::Expr::value_var(id.clone()),
                    )
                });
                let e = expr::Expr::Record(mids.chain(vids).collect());
                Ok((
                    ExSig::quantify(table, whole_fvs, whole_sig),
                    expr::Expr::r#let(v, e),
                ))
            }
            el::Module::Proj(m, id) => {
                let (exsig, e) = m.elaborate(env, table)?;
                Ok((
                    exsig.try_map(|sig| sig.proj_module(&id))?,
                    expr::Expr::proj_module(e, id),
                ))
            }
            el::Module::Curtail(x, s) => {
                let (exsig, e) = x.elaborate(env, table)?;
                let fsig = s.elaborate(env, table)?;

                let (fvs, sig) = exsig.get_body(table);
                let tys = sig.r#match(table, &fsig)?;
                Ok((
                    ExSig::quantify(table, fvs, fsig.instantiate(table, &tys)),
                    e,
                ))
            }
            el::Module::Seal(x, s) => {
                let (exsig, e) = x.elaborate(env, table)?;
                let fsig = s.elaborate(env, table)?;

                let (_, sig) = exsig.get_body(table);
                let _ = sig.r#match(table, &fsig)?;
                Ok((ExSig::from(fsig), e))
            }
        }
    }
}

impl Elaborate for el::Binding {
    type Output = (ExSig, Option<expr::Binding>);

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output> {
        match self {
            el::Binding::Module(id, m) => {
                let (exsig, e) = m.elaborate(env, table)?;
                Ok((
                    exsig.map(|sig| Sig::singleton_module(id.clone(), sig)),
                    Some(expr::Binding::Var(expr::Var::Module(id), e)),
                ))
            }
            el::Binding::Signature(id, s) => {
                let fsig = s.elaborate(env, table)?;
                Ok((ExSig::from(Sig::singleton_signature(id, fsig)), None))
            }
            el::Binding::Value(id, e) => {
                let (a, e) = e.elaborate(env, table)?;
                let scheme = Scheme::gen(table, env.get_rank(), a);
                Ok((
                    ExSig::from(Sig::singleton_value(id.clone(), scheme)),
                    Some(expr::Binding::Var(expr::Var::Value(id), e)),
                ))
            }
            el::Binding::Type(id, ty) => {
                let (k, ty) = ty.elaborate(env, table)?;
                Ok((ExSig::from(Sig::singleton_type(id, (ty, k))), None))
            }
            el::Binding::Include(m) => {
                let (exsig, e) = m.elaborate(env, table)?;
                let mids = exsig.get_module_identifiers().map(|id| {
                    (
                        expr::Label::Module(id.clone()),
                        expr::Var::Module(id.clone()),
                    )
                });
                let vids = exsig
                    .get_value_identifiers()
                    .map(|id| (expr::Label::Value(id.clone()), expr::Var::Value(id.clone())));
                let map = mids.chain(vids).collect();
                Ok((exsig, Some(expr::Binding::Record(map, e))))
            }
        }
    }
}

impl Elaborate for el::Signature {
    type Output = Family;

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output> {
        match self {
            el::Signature::Ident(id) => Ok(env.lookup_signature(&id)?),
            el::Signature::Seq(ds) => {
                let mut env = env.clone();
                let mut whole_xs = Vec::new();
                let mut whole_sig = Sig::default();
                for d in ds {
                    let fsig = d.elaborate(&env, table)?;

                    let (xs, sig) = fsig.get_body(table);
                    whole_xs.extend(xs);
                    whole_sig.insert_disjoint(sig.clone())?;
                    env.insert(sig);
                }

                Ok(Family::quantify(table, whole_xs, whole_sig))
            }
            el::Signature::Proj(m, id) => {
                let (exsig, _) = m.elaborate(env, table)?;
                exsig.escape(table, |sig| Ok(sig.proj_signature(&id)?))
            }
            el::Signature::WhereType(x, loc, ty) => {
                let fsig = x.elaborate(env, table)?;
                let (k1, ty1) = ty.elaborate(env, table)?;
                let (xs, mut sig) = fsig.get_body(table);
                let (ty, k) = sig.proj_type_loc(&loc)?;

                k.unify(&k1)?;

                for (i, (fv, _)) in xs.iter().enumerate() {
                    // Note that we don't need to care about unification.
                    if ty == Tycon::eta(fv.clone()) {
                        sig.subst(table, fv.clone(), ty1);
                        let mut ys = xs;
                        ys.remove(i);
                        return Ok(Family::quantify(table, ys, sig));
                    }
                }
                Err(From::from(ElaborateError::RefiningOuterType(loc, sig)))
            }
        }
    }
}

impl Elaborate for el::Decl {
    type Output = Family;

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output> {
        match self {
            el::Decl::Module(id, s) => {
                let fsig = s.elaborate(env, table)?;
                Ok(fsig.map(
                    |Loc(mut mids, tid)| {
                        mids.insert(0, id.clone());
                        Loc(mids, tid)
                    },
                    |sig| Sig::singleton_module(id.clone(), sig),
                ))
            }
            el::Decl::Signature(id, s) => {
                let fsig = s.elaborate(env, table)?;
                Ok(Family::from(Sig::singleton_signature(id, fsig)))
            }
            el::Decl::Value(id, scheme) => {
                let scheme = scheme.elaborate(env, table)?;
                Ok(Family::from(Sig::singleton_value(id, scheme)))
            }
            el::Decl::TypeTrans(id, ty) => {
                let (k, ty) = ty.elaborate(env, table)?;
                Ok(Family::from(Sig::singleton_type(id, (ty, k))))
            }
            el::Decl::Type(id, k) => {
                let fv = table.fresh_fvar(k.clone());
                Ok(Family::quantify(
                    table,
                    vec![(fv.clone(), Loc(vec![], id.clone()))],
                    Sig::singleton_type(id, (Tycon::eta(fv), k)),
                ))
            }
            el::Decl::Include(s) => s.elaborate(env, table),
        }
    }
}

impl Elaborate for el::Expr {
    type Output = (Atom, expr::Expr);

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output> {
        match self {
            el::Expr::Ident(id) => Ok((
                env.lookup_value(&id)?.instantiate(table),
                expr::Expr::value_var(id),
            )),
            el::Expr::Proj(m, id) => {
                let (exsig, e) = m.elaborate(env, table)?;
                let scheme = exsig.escape(table, |sig| Ok(sig.proj_value(&id)?))?;
                Ok((scheme.instantiate(table), expr::Expr::proj_value(e, id)))
            }
            el::Expr::Abs(id, x) => {
                let mut env = env.clone();
                env.increment_rank();
                let rank = env.get_rank();
                let uv = Atom::Unif(table.fresh_uvar(rank));
                env.insert_value(id.clone(), Scheme::from(uv.clone()));

                let (ty, e) = x.elaborate(&env, table)?;
                Ok((Atom::arrow(uv, ty), expr::Expr::abs(id, e)))
            }
            el::Expr::App(x, y) => {
                let (ty1, e1) = x.elaborate(env, table)?;
                let (ty2, e2) = y.elaborate(env, table)?;
                let uv = Atom::Unif(table.fresh_uvar(Rank::Infinity));
                ty1.unify(table, &Atom::arrow(ty2, uv.clone()))?;

                Ok((uv, expr::Expr::app(e1, e2)))
            }
        }
    }
}

impl Elaborate for el::Tycon {
    type Output = (Kind, Tycon);

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output> {
        match self {
            el::Tycon::Ident(id) => {
                let (ty, k) = env.lookup_type(&id)?;
                Ok((k, ty))
            }
            el::Tycon::Proj(m, id) => {
                let (exsig, _) = m.elaborate(env, table)?;
                let (ty, k) = exsig.escape(table, |sig| Ok(sig.proj_type(&id)?))?;
                Ok((k, ty))
            }
            el::Tycon::Var(tv) => {
                let fv = env.lookup_type_var(&tv)?;
                Ok((fv.clone().get_kind(), Tycon::fvar(fv)))
            }
            el::Tycon::Abs(tv, x) => {
                let fv = table.fresh_fvar(Kind::Base);
                let mut env = env.clone();
                env.insert_type_var(tv, fv.clone());
                let (k, ty) = x.elaborate(&env, table)?;
                Ok((Kind::arrow(k), Tycon::abs(table, fv, ty)))
            }
            el::Tycon::App(x, y) => {
                let (k1, ty1) = x.elaborate(env, table)?;
                let (k2, ty2) = y.elaborate(env, table)?;
                let a2 = ty2.get_atom(k2)?;

                let (ty, k) = ty1.beta(table, k1, a2)?;

                Ok((k, ty))
            }
            el::Tycon::Arrow(x, y) => {
                let (k1, ty1) = x.elaborate(env, table)?;
                let a1 = ty1.get_atom(k1)?;
                let (k2, ty2) = y.elaborate(env, table)?;
                let a2 = ty2.get_atom(k2)?;

                Ok((Kind::Base, Tycon::arrow(a1, a2)))
            }
        }
    }
}

impl Elaborate for el::Scheme {
    type Output = Scheme;

    fn elaborate(self, env: &Env, table: &mut UnifTable) -> Result<Self::Output> {
        let mut s = self;
        let mut env = env.clone();
        let mut fvs = Vec::new();
        loop {
            match s {
                el::Scheme::Body(ty) => {
                    let (k, ty) = ty.elaborate(&env, table)?;
                    return Ok(Scheme::quantify(table, fvs, ty.get_atom(k)?));
                }
                el::Scheme::Forall(tv, scheme) => {
                    let fv = table.fresh_fvar(Kind::Base);
                    fvs.push(fv.clone());
                    env.insert_type_var(tv, fv);
                    s = *scheme;
                }
            }
        }
    }
}
