mod flags;
pub mod instruction;
mod lexer;
mod register;
pub mod token;

pub use flags::Flags;
pub use lexer::Lexer;
pub use register::Register;
pub use token::*;

use thiserror::Error;

pub type LexResult<T> = Result<T, LexError>;

#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum LexError {
  /// The lexer encountered invalid UTF-8.
  #[error("invalid utf-8 encountered at position `{0}`")]
  InvalidUtf8(usize),
}

/// Lexes the input source into a group of tokens.
pub fn lex(src: &str) -> LexResult<Vec<Token>> {
  Lexer::from_string(src).into_iter().collect()
}
