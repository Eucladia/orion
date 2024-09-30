use std::ops::Range;

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug, Clone)]
pub struct ParseError {
  /// The position where the error ocurred.
  pub location: Range<usize>,
  /// The kind of error.
  // pub error_kind: ErrorKind,
  /// The error message.
  // For more concise error messages
  pub error_message: String,
}

pub enum ErrorKind {}

impl std::fmt::Display for ParseError {
  fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(fmt, "{}", &self.error_message)
  }
}

// TODO: Figure out if implementation of Error trait is good
impl std::error::Error for ParseError {}
