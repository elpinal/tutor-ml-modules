pub mod el;
pub mod elaboration;
pub mod env;
pub mod ident;
pub mod il;
pub mod kind;
mod paren;
pub mod parser;
pub mod token;

use crate::elaboration::Elaborate;

use anyhow::Result;
use logos::Logos;

fn lex(s: &str) -> Result<Vec<token::Token>> {
    let mut lexer = token::Token::lexer(s);
    let mut tokens = Vec::new();
    loop {
        match lexer.next() {
            None => return Ok(tokens),
            Some(token::Token::Error) => {
                let span = lexer.span();
                let s = lexer.slice();
                return Err(anyhow::anyhow!(
                    "{}.{}: unexpected: {}",
                    span.start,
                    span.end,
                    s
                ));
            }
            Some(t) => tokens.push(t),
        }
    }
}

pub fn parse_string(s: &str) -> Result<el::Module> {
    let tokens = lex(s)?;
    let bs = parser::parse(&tokens)?;
    Ok(el::Module::Seq(bs))
}

pub fn elaborate(
    table: &mut il::tycon::UnifTable,
    m: el::Module,
) -> Result<(il::sig::ExSig, il::expr::Expr)> {
    m.elaborate(&env::Env::initial(), table)
}
