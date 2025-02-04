pub mod nodes;
pub mod parser;

use nodes::ProgramNode;
use orion_lexer::Token;

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

/// Parses a program from the given source and tokens.
pub fn parse_tokens(src: &str, tokens: Vec<Token>) -> orion_types::ParseResult<ProgramNode> {
  Parser::new(src, tokens).parse()
}

/// Parses a program from the given source.
pub fn parse(src: &str) -> orion_types::Result<ProgramNode> {
  Ok(parse_tokens(src, orion_lexer::lex(src)?)?)
}
