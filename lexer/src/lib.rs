mod flags;
pub mod instruction;
mod lexer;
mod register;
pub mod token;

pub use flags::Flags;
pub use lexer::Lexer;
pub use register::Register;

use thiserror::Error;

pub type LexerResult<T> = std::result::Result<T, LexerError>;

#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum LexerError {
  /// The lexer encountered invalid UTF-8.
  #[error("invalid utf-8 encountered at position `{0}`")]
  InvalidUtf8(usize),
}
