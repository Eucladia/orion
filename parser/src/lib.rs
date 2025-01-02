pub mod nodes;
pub mod parser;

use lexer::Token;
use nodes::ProgramNode;
use types::ParseResult;

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

pub fn parse_tokens(src: &str, tokens: Vec<Token>) -> ParseResult<ProgramNode> {
  let mut parser = parser::Parser::new(src, tokens);

  parser.parse()
}

pub fn parse(src: &str) -> types::Result<ProgramNode> {
  match lexer::lex(src) {
    Ok(tokens) => match parse_tokens(src, tokens) {
      Ok(node) => Ok(node),
      Err(err) => Err(types::Error::Parser(err)),
    },
    Err(err) => Err(types::Error::Lexer(err)),
  }
}
