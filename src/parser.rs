#![allow(clippy::redundant_closure_call)]

use crate::el;
use crate::el::*;
use crate::token::Token;
use crate::token::Token::*;

peg::parser! {
    grammar el_parser() for [Token] {
        rule module_ident() -> ModuleIdent
            = [UpperIdent(id)] { ModuleIdent::from(id) }

        rule signature_ident() -> SignatureIdent
            = [UpperIdent(id)] { SignatureIdent::from(id) }

        rule value_ident() -> ValueIdent
            = [LowerIdent(id)] { ValueIdent::from(id) }

        rule type_ident() -> TypeIdent
            = [LowerIdent(id)] { TypeIdent::from(id) }

        rule type_loc() -> Loc<TypeIdent>
            = tid:type_ident() { Loc(Vec::new(), tid) }
            / mids:(module_ident() ** [Dot]) [Dot] tid:type_ident() { Loc(mids, tid) }

        rule type_var() -> TypeVar
            = [QuoteIdent(id)] { TypeVar::from(id) }


        rule module() -> el::Module = quiet!{precedence!{
            m:@ [Colon] s:sig()   { el::Module::Curtail(Box::new(m), s) }
            m:@ [ColonGT] s:sig() { el::Module::Seal(Box::new(m), s) }
            --
            m:@ [Dot] id:module_ident() { el::Module::Proj(Box::new(m), id) }
            --
            [LParen] m:module() [RParen]    { m }
            id:module_ident()               { el::Module::Ident(id) }
            [LBrace] bs:bindings() [RBrace] { el::Module::Seq(bs) }
        }} / expected!("module")

        rule binding() -> Binding
            = [Module] id:module_ident() [Equal] m:module()    { Binding::Module(id, m) }
            / [Signature] id:signature_ident() [Equal] s:sig() { Binding::Signature(id, s) }
            / [Val] id:value_ident() [Equal] e:expr()          { Binding::Value(id, e) }
            / [Type] id:type_ident() ty:type_abs()             { Binding::Type(id, ty) }
            / [Include] m:module()                             { Binding::Include(m) }

        pub rule bindings() -> Vec<Binding>
            = bs:binding()*

        rule sig() -> el::Signature = precedence!{
            s:@ [Where] [Type] loc:type_loc() ty:type_abs()
                { el::Signature::WhereType(Box::new(s), loc, ty) }
            --
            m:module() [Dot] id:signature_ident() { el::Signature::Proj(Box::new(m), id) }
            --
            [LParen] s:sig() [RParen] { s }
            id:signature_ident()      { el::Signature::Ident(id) }
            [Sig] ds:decl()* [End]    { el::Signature::Seq(ds) }
        }

        rule type_abs() -> Tycon
            = tvs:type_var()* [Equal] ty:r#type() {? el::Tycon::abs(tvs, ty) }

        rule decl() -> Decl
            = [Module] id:module_ident() [Colon] s:sig()       { Decl::Module(id, s) }
            / [Signature] id:signature_ident() [Equal] s:sig() { Decl::Signature(id, s) }
            / [Include] s:sig()                                { Decl::Include(s) }
            / [Val] id:value_ident() tvs:type_var()* [Colon] ty:r#type()
                {? Decl::value(id, tvs, ty) }
            / [Type] id:type_ident() tvs:type_var()* ty:eq_type()?
                {? Decl::r#type(id, tvs, ty) }

        rule eq_type() -> Tycon =
            [Equal] ty:r#type() { ty }

        rule expr() -> Expr = precedence!{
            [Lambda] id:value_ident() [RDArrow] e:@ { Expr::Abs(id, Box::new(e)) }
            --
            es:expr_atom()+
                { es.into_iter().reduce(|acc, e| Expr::App(Box::new(acc), Box::new(e))).unwrap() }
        }

        rule expr_atom() -> Expr = precedence!{
            m:module() [Dot] id:value_ident() { Expr::Proj(Box::new(m), id) }
            --
            [LParen] e:expr() [RParen] { e }
            id:value_ident() { Expr::Ident(id) }
        }

        rule r#type() -> Tycon = quiet!{precedence!{
            [Lambda] tv:type_var() [RDArrow] ty:@ { Tycon::Abs(tv, Box::new(ty)) }
            --
            x:@ [RArrow] y:(@) { Tycon::Arrow(Box::new(x), Box::new(y)) }
            --
            tys:type_atom()+
                { tys.into_iter().reduce(|acc, ty| Tycon::App(Box::new(acc), Box::new(ty))).unwrap() }
        }} / expected!("type")

        rule type_atom() -> Tycon = precedence!{
            m:module() [Dot] id:type_ident() { Tycon::Proj(Box::new(m), id) }
            --
            [LParen] ty:r#type() [RParen] { ty }
            id:type_ident() { Tycon::Ident(id) }
            tv:type_var()   { Tycon::Var(tv) }
        }
    }
}

pub fn parse(tokens: &[Token]) -> Result<Vec<Binding>, peg::error::ParseError<usize>> {
    el_parser::bindings(tokens)
}
