pub mod nodes;
pub mod parser;

use lexer::Token;
use nodes::ProgramNode;

pub use parser::Parser;

#[macro_export]
macro_rules! unwrap {
  ($expr:expr) => {{
    #[cfg(debug_assertions)]
    {
      $expr.unwrap()
    }
    #[cfg(not(debug_assertions))]
    unsafe {
      $expr.unwrap_unchecked()
    }
  }};
}

pub fn parse_tokens(src: &str, tokens: Vec<Token>) -> types::ParseResult<ProgramNode> {
  Parser::new(src, tokens).parse()
}

pub fn parse(src: &str) -> types::Result<ProgramNode> {
  Ok(parse_tokens(src, lexer::lex(src)?)?)
}
