use std::ops::Range;
use thiserror::Error;

/// A lex result.
pub type LexResult<T> = std::result::Result<T, LexError>;

/// A parse result.
pub type ParseResult<T> = std::result::Result<T, ParseError>;

pub type Result<T> = std::result::Result<T, Error>;

/// An error.
#[derive(Debug)]
pub enum Error {
  Lexer(LexError),
  Parser(ParseError),
}
/// An error that occurred during lexing.
#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum LexError {
  /// The lexer encountered invalid UTF-8.
  #[error("invalid utf-8 encountered at position `{0}`")]
  InvalidUtf8(usize),
}

/// An error that occurred during parsing.
#[derive(Debug, Clone)]
pub struct ParseError {
  /// The position where the error ocurred.
  pub location: Range<usize>,
  /// The error message.
  pub error_message: String,
}
