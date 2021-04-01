pub use crate::kind::Kind;
use crate::paren::Paren;

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::mem;

use anyhow::Result;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FVar(usize, Kind);

impl fmt::Display for FVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "!v{}", self.0)
    }
}

pub struct FVars(pub Vec<FVar>);

impl fmt::Display for FVars {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0.is_empty() {
            return Ok(());
        }
        write!(f, "{}", self.0[0])?;
        if self.0.len() == 1 {
            return Ok(());
        }

        for fv in &self.0[1..] {
            write!(f, " {}", fv)?;
        }
        Ok(())
    }
}

impl FVar {
    pub fn get_kind(self) -> Kind {
        self.1
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UVar(usize);

impl fmt::Display for UVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "?u{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rank {
    Nat(usize),
    Infinity,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    Bound(usize, usize),
    Free(FVar),
    Unif(UVar),
    App(Box<Atom>, Box<Atom>),
    Arrow(Box<Atom>, Box<Atom>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Tycon {
    Abs(Box<Tycon>),
    Body(Atom),
}

enum UnifStatus {
    Undefined(Rank),
    Defined(Atom),
}

#[derive(Default)]
pub struct UnifTable {
    m: HashMap<UVar, UnifStatus>,
    uvar_counter: usize,
    fvar_counter: usize,
}

impl UnifTable {
    pub fn fresh_uvar(&mut self, rank: Rank) -> UVar {
        let uv = UVar(self.uvar_counter);
        self.uvar_counter += 1;
        self.m.insert(uv, UnifStatus::Undefined(rank));
        uv
    }

    pub fn fresh_fvar(&mut self, k: Kind) -> FVar {
        let n = self.fvar_counter;
        self.fvar_counter += 1;
        FVar(n, k)
    }

    fn lookup(&self, uv: UVar) -> &UnifStatus {
        self.m.get(&uv).expect("inconsitency of unification table")
    }

    fn get_rank(&self, uv: UVar) -> Rank {
        match *self.lookup(uv) {
            UnifStatus::Undefined(r) => r,
            UnifStatus::Defined(_) => panic!("defined"),
        }
    }

    fn unify_var(&mut self, uv: UVar, with: &Atom) -> Result<()> {
        if let Atom::Unif(uv2) = *with {
            if uv == uv2 {
                return Ok(());
            }
        }
        self.occur_check(uv, self.get_rank(uv), with)?;
        self.m.insert(uv, UnifStatus::Defined(with.clone()));
        Ok(())
    }

    fn occur_check(&mut self, uv: UVar, r: Rank, a: &Atom) -> Result<()> {
        use Atom::*;
        match *a {
            Bound(..) => (),
            Free(..) => (),
            Unif(uv2) => {
                if uv == uv2 {
                    anyhow::bail!("occur check: recursive type");
                }
                let r2 = self.get_rank(uv2);
                if r < r2 {
                    self.m.insert(uv2, UnifStatus::Undefined(r));
                }
            }
            App(ref x, ref y) => {
                // Note that `x` has a non-base kind so it cannot be a unification variable.
                self.occur_check(uv, r, x)?;
                self.occur_check(uv, r, y.unroll(self).as_ref())?;
            }
            Arrow(ref x, ref y) => {
                self.occur_check(uv, r, x.unroll(self).as_ref())?;
                self.occur_check(uv, r, y.unroll(self).as_ref())?;
            }
        }
        Ok(())
    }
}

pub trait DisplayTable {
    fn fmt_with_table(&self, f: &mut fmt::Formatter, table: &mut UnifTable) -> fmt::Result;
}

pub struct DisplayTableWrapper<T>(pub T);

impl<T: DisplayTable> fmt::Display for DisplayTableWrapper<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt_with_table(f, &mut Default::default())
    }
}

pub trait Close {
    fn close(&mut self, table: &UnifTable, j: usize, fvs: &[FVar]);
}

pub trait Open {
    fn open(&mut self, table: &UnifTable, j: usize, tys: &[Tycon]);
}

pub trait Unify {
    fn unify(&self, table: &mut UnifTable, with: &Self) -> Result<()>;
}

pub trait Find {
    fn find_bound(&self, table: &UnifTable, j: usize) -> Result<()>;
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Atom::*;
        // unroll?
        match self {
            Bound(..) => panic!("not locally closed"),
            Free(fv) => write!(f, "{}", fv),
            Unif(uv) => write!(f, "{}", uv),
            App(x, y) => write!(f, "{} {}", Paren(5, x.prec(), x), Paren(4, y.prec(), y)),
            Arrow(x, y) => write!(f, "{} -> {}", Paren(6, x.prec(), x), Paren(7, y.prec(), y)),
        }
    }
}

impl Close for Atom {
    fn close(&mut self, table: &UnifTable, j: usize, fvs: &[FVar]) {
        use Atom::*;
        match *self {
            Bound(..) => {}
            Free(ref fv) => {
                if let Some(i) = fvs.iter().position(|v| fv == v) {
                    *self = Bound(j, i);
                }
            }
            Unif(uv) => match table.lookup(uv) {
                UnifStatus::Undefined(_) => {}
                UnifStatus::Defined(ty) => {
                    *self = ty.clone();
                    self.close(table, j, fvs);
                }
            },
            App(ref mut x, ref mut y) => {
                x.close(table, j, fvs);
                y.close(table, j, fvs)
            }
            Arrow(ref mut x, ref mut y) => {
                x.close(table, j, fvs);
                y.close(table, j, fvs)
            }
        }
    }
}

impl Unify for Atom {
    fn unify(&self, table: &mut UnifTable, with: &Self) -> Result<()> {
        use Atom::*;
        match (self.unroll(table).as_ref(), with.unroll(table).as_ref()) {
            (&Unif(uv), _) => table.unify_var(uv, with)?,
            (_, &Unif(uv)) => table.unify_var(uv, with)?,
            (&Bound(n, i), &Bound(m, j)) if n == m && i == j => {}
            (&Free(ref fv1), &Free(ref fv2)) if fv1 == fv2 => {}
            (&App(ref x1, ref y1), &App(ref x2, ref y2)) => {
                x1.unify(table, x2)?;
                y1.unify(table, y2)?;
            }
            (&Arrow(ref x1, ref y1), &Arrow(ref x2, ref y2)) => {
                x1.unify(table, x2)?;
                y1.unify(table, y2)?;
            }
            _ => anyhow::bail!("cannot unify"),
        }
        Ok(())
    }
}

impl Find for Atom {
    fn find_bound(&self, table: &UnifTable, j: usize) -> Result<()> {
        use Atom::*;
        match self.unroll(table).as_ref() {
            Bound(n, i) if *n == j => Err(anyhow::anyhow!("found a bound variable ({}, {})", n, i)),
            Bound(..) | Free(_) | Unif(_) => Ok(()),
            App(x, y) => {
                x.find_bound(table, j)?;
                y.find_bound(table, j)
            }
            Arrow(x, y) => {
                x.find_bound(table, j)?;
                y.find_bound(table, j)
            }
        }
    }
}

impl Atom {
    pub fn app(x: Atom, y: Atom) -> Atom {
        Atom::App(Box::new(x), Box::new(y))
    }

    pub fn arrow(x: Atom, y: Atom) -> Atom {
        Atom::Arrow(Box::new(x), Box::new(y))
    }

    fn prec(&self) -> usize {
        use Atom::*;
        match self {
            Bound(..) | Free(..) | Unif(..) => 0,
            App(..) => 4,
            Arrow(..) => 6,
        }
    }

    fn open(self, table: &UnifTable, j: usize, tys: &[Tycon]) -> Tycon {
        use Atom::*;
        match self {
            Bound(n, i) => {
                if n == j {
                    tys[i].clone()
                } else {
                    Tycon::Body(self)
                }
            }
            Free(_) => Tycon::Body(self),
            Unif(uv) => match table.lookup(uv) {
                UnifStatus::Defined(a) => a.clone().open(table, j, tys),
                UnifStatus::Undefined(_) => Tycon::Body(self),
            },
            App(x, mut y) => {
                y.open_as_atom(table, j, tys);
                match x.open(table, j, tys) {
                    Tycon::Body(a) => Tycon::Body(App(Box::new(a), y)),
                    Tycon::Abs(mut ty) => {
                        ty.open(table, 0, &[Tycon::Body(*y)]);
                        *ty
                    }
                }
            }
            Arrow(mut x, mut y) => {
                x.open_as_atom(table, j, tys);
                y.open_as_atom(table, j, tys);
                Tycon::Body(Arrow(x, y))
            }
        }
    }

    pub fn open_as_atom(&mut self, table: &UnifTable, j: usize, tys: &[Tycon]) {
        let ty = mem::replace(self, Atom::Bound(0, 0));
        match ty.open(table, j, tys) {
            Tycon::Body(a) => *self = a,
            Tycon::Abs(_) => panic!("open_as_atom is a total function for types of kind `Type`."),
        }
    }

    fn unroll(&self, table: &UnifTable) -> Cow<Self> {
        match *self {
            Atom::Unif(uv) => match table.lookup(uv) {
                UnifStatus::Defined(a) => Cow::Owned(a.unroll(table).into_owned()),
                UnifStatus::Undefined(_) => Cow::Borrowed(self),
            },
            _ => Cow::Borrowed(self),
        }
    }

    // Replace unification variables, whose rank is greater than a given rank, with fresh free
    // variables.
    pub fn replace_uvars(&mut self, table: &mut UnifTable, rank: Rank, fvs: &mut Vec<FVar>) {
        use Atom::*;
        match self {
            Bound(..) | Free(_) => (),
            Unif(uv) => match table.lookup(*uv) {
                UnifStatus::Defined(a) => {
                    let mut a = a.clone();
                    a.replace_uvars(table, rank, fvs);
                    *self = a;
                }
                UnifStatus::Undefined(rank1) => {
                    if *rank1 > rank {
                        let fv = table.fresh_fvar(Kind::Base);
                        fvs.push(fv.clone());
                        table.m.insert(*uv, UnifStatus::Defined(Atom::Free(fv)));
                    }
                }
            },
            App(x, y) => {
                x.replace_uvars(table, rank, fvs);
                y.replace_uvars(table, rank, fvs);
            }
            Arrow(x, y) => {
                x.replace_uvars(table, rank, fvs);
                y.replace_uvars(table, rank, fvs);
            }
        }
    }
}

impl DisplayTable for Tycon {
    fn fmt_with_table(&self, f: &mut fmt::Formatter, table: &mut UnifTable) -> fmt::Result {
        use Tycon::*;
        match self {
            Body(a) => write!(f, "{}", a),
            Abs(ty) => {
                let fv = table.fresh_fvar(Kind::Base);
                write!(f, "λ{} => ", fv)?;

                let mut ty = ty.clone();
                ty.open(table, 0, &[Tycon::fvar(fv)]);
                ty.fmt_with_table(f, table)
            }
        }
    }
}

impl Close for Tycon {
    fn close(&mut self, table: &UnifTable, j: usize, fvs: &[FVar]) {
        use Tycon::*;
        match *self {
            Body(ref mut a) => a.close(table, j, fvs),
            Abs(ref mut ty) => ty.close(table, j + 1, fvs),
        }
    }
}

impl Open for Tycon {
    fn open(&mut self, table: &UnifTable, j: usize, tys: &[Tycon]) {
        use Tycon::*;
        match *self {
            Abs(ref mut ty) => ty.open(table, j + 1, tys),
            Body(ref mut a) => {
                let a1 = mem::replace(a, Atom::Bound(0, 0));
                let ty = a1.open(table, j, tys);
                *self = ty;
            }
        }
    }
}

impl Unify for Tycon {
    fn unify(&self, table: &mut UnifTable, with: &Self) -> Result<()> {
        use Tycon::*;
        match (self, with) {
            (&Body(ref x), &Body(ref y)) => x.unify(table, y),
            (&Abs(ref x), &Abs(ref y)) => x.unify(table, y),
            _ => Err(anyhow::anyhow!("cannot unify")),
        }
    }
}

impl Find for Tycon {
    fn find_bound(&self, table: &UnifTable, j: usize) -> Result<()> {
        use Tycon::*;
        match self {
            Body(a) => a.find_bound(table, j),
            Abs(ty) => ty.find_bound(table, j + 1),
        }
    }
}

impl Tycon {
    pub fn abs(table: &UnifTable, fv: FVar, mut x: Tycon) -> Tycon {
        x.close(table, 0, &[fv]);
        Tycon::Abs(Box::new(x))
    }

    // Don't use this function unless you are really confident that
    // `fv` has the base kind.
    // Use `Tycon::eta()` instead if `fv` may have a non-base kind.
    pub fn fvar(fv: FVar) -> Tycon {
        Tycon::Body(Atom::Free(fv))
    }

    pub fn arrow(x: Atom, y: Atom) -> Tycon {
        Tycon::Body(Atom::arrow(x, y))
    }

    pub fn eta(fv: FVar) -> Tycon {
        let n = usize::from(&fv.1);

        let a = (0..n)
            .rev()
            .fold(Atom::Free(fv), |a, i| Atom::app(a, Atom::Bound(i, 0)));

        (0..n).fold(Tycon::Body(a), |ty, _| Tycon::Abs(Box::new(ty)))
    }

    pub fn get_atom(self, k: Kind) -> Result<Atom> {
        match (k, self) {
            (Kind::Base, Tycon::Body(a)) => Ok(a),
            _ => Err(anyhow::anyhow!("not base kind")),
        }
    }

    // Input:
    //   `self` : `k`
    //   `a` : Type
    // Output:
    //   ([`a`/α]c, k')  if (`self` = λα. c) and (`k` = Type -> k').
    //   error           otherwise.
    pub fn beta(self, table: &UnifTable, k: Kind, a: Atom) -> Result<(Tycon, Kind)> {
        match (k, self) {
            (Kind::Arrow(k1), Tycon::Abs(mut ty)) => {
                ty.open(table, 0, &[Tycon::Body(a)]);
                Ok((*ty, *k1))
            }
            _ => Err(anyhow::anyhow!("not arrow kind")),
        }
    }
}
