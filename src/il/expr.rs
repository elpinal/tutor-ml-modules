#![allow(dead_code)]

use crate::ident::*;
use crate::paren::Paren;

use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug)]
pub enum Var {
    Module(ModuleIdent),
    Value(ValueIdent),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Label {
    Module(ModuleIdent),
    Value(ValueIdent),
}

#[derive(Debug)]
pub enum Expr {
    Var(Var),
    Abs(Var, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Record(BTreeMap<Label, Expr>),
    Proj(Box<Expr>, Label),
    Let(Vec<Binding>, Box<Expr>),
}

#[derive(Debug)]
pub enum Binding {
    Var(Var, Expr),
    Record(BTreeMap<Label, Var>, Expr),
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Var::Module(id) => id.fmt(f),
            Var::Value(id) => id.fmt(f),
        }
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Label::Module(id) => id.fmt(f),
            Label::Value(id) => id.fmt(f),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Expr::*;
        match self {
            Var(v) => write!(f, "{}", v),
            Abs(v, x) => {
                write!(f, "λ{} => {}", v, x)
            }
            App(x, y) => {
                write!(f, "{} {}", Paren(5, x.prec(), x), Paren(4, y.prec(), y))
            }
            Record(m) => {
                write!(f, "{{")?;
                for (i, (l, e)) in m.iter().enumerate() {
                    write!(f, "{} = {}", l, e)?;
                    if i + 1 != m.len() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "}}")?;
                Ok(())
            }
            Proj(x, l) => {
                write!(f, "{}.{}", Paren(1, x.prec(), x), l)
            }
            Let(bs, x) => {
                write!(f, "let")?;
                for (i, b) in bs.iter().enumerate() {
                    if i != 0 {
                        write!(f, ";")?;
                    }
                    write!(f, " {}", b)?;
                }
                write!(f, " in {}", x)?;
                Ok(())
            }
        }
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Binding::Var(v, e) => write!(f, "{} = {}", v, e),
            Binding::Record(m, e) => {
                write!(f, "{{")?;
                for (i, (l, e)) in m.iter().enumerate() {
                    write!(f, "{} = {}", l, e)?;
                    if i + 1 != m.len() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "}} = {}", e)?;
                Ok(())
            }
        }
    }
}

impl Expr {
    pub fn module_var(id: ModuleIdent) -> Self {
        Expr::Var(Var::Module(id))
    }

    pub fn value_var(id: ValueIdent) -> Self {
        Expr::Var(Var::Value(id))
    }

    pub fn proj_module(e: Expr, id: ModuleIdent) -> Self {
        Expr::Proj(Box::new(e), Label::Module(id))
    }

    pub fn proj_value(e: Expr, id: ValueIdent) -> Self {
        Expr::Proj(Box::new(e), Label::Value(id))
    }

    pub fn abs(id: ValueIdent, x: Expr) -> Self {
        Expr::Abs(Var::Value(id), Box::new(x))
    }

    pub fn app(x: Expr, y: Expr) -> Self {
        Expr::App(Box::new(x), Box::new(y))
    }

    pub fn r#let(bs: Vec<Binding>, x: Expr) -> Self {
        Expr::Let(bs, Box::new(x))
    }

    fn prec(&self) -> usize {
        use Expr::*;
        match self {
            Var(..) => 0,
            Abs(..) => 9,
            App(..) => 4,
            Record(..) => 0,
            Proj(..) => 0,
            Let(..) => 9,
        }
    }
}
