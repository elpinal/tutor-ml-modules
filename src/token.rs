use logos::Logos;

#[derive(Logos, Clone, Debug, PartialEq)]
pub enum Token {
    #[regex("[A-Z][a-zA-Z0-9_]*", |x| x.slice().to_string())]
    UpperIdent(String),
    #[regex("[a-z][a-zA-Z0-9_]*", |x| x.slice().to_string())]
    LowerIdent(String),
    #[regex("'[a-z][a-zA-Z0-9_]*", |x| x.slice().to_string())]
    QuoteIdent(String),

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,

    #[token(".")]
    Dot,
    #[token(":")]
    Colon,
    #[token(":>")]
    ColonGT,
    #[token("=")]
    Equal,
    #[token("->")]
    RArrow,
    #[token("=>")]
    RDArrow,

    #[token("module")]
    Module,
    #[token("signature")]
    Signature,
    #[token("val")]
    Val,
    #[token("type")]
    Type,
    #[token("include")]
    Include,
    #[token("where")]
    Where,
    #[token("sig")]
    Sig,
    #[token("end")]
    End,

    #[token("λ")]
    Lambda,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}
