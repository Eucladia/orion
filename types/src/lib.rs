use thiserror::Error;

/// A lex result.
pub type LexResult<T> = std::result::Result<T, LexError>;

/// A parse result.
pub type ParseResult<T> = std::result::Result<T, ParseError>;

/// A result.
pub type Result<T> = std::result::Result<T, Error>;

/// An error.
#[derive(Debug, Error)]
pub enum Error {
  #[error("an error occured during lexing")]
  Lexer(#[from] LexError),
  #[error("an error occured during parsing")]
  Parser(#[from] ParseError),
}
/// An error that occurred during lexing.
#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum LexError {
  /// The lexer encountered invalid UTF-8.
  #[error("invalid utf-8 encountered at position `{0}`")]
  InvalidUtf8(usize),
}

/// An error that occurred during parsing.
#[derive(Debug, Error, Clone)]
#[error("parsing error occurred at {start_pos}: {kind}")]
pub struct ParseError {
  /// The position where the error ocurred.
  pub start_pos: usize,
  /// The error message.
  pub kind: ParserErrorKind,
}

#[derive(Debug, Clone, Copy, Error)]
pub enum ParserErrorKind {
  #[error("the symbol is reserved")]
  ReservedSymbol,

  #[error("the length of the label name is invalid")]
  LabelNameSizeInvalid,

  #[error("label already defined")]
  LabelAlreadyDefined,

  #[error("unexpected token")]
  UnexpectedToken,

  #[error("invalid operand provided")]
  InvalidOperand,

  #[error("expected an operand")]
  ExpectedOperand,

  #[error("invalid operand type")]
  InvalidOperandType,

  #[error("invalid number")]
  InvalidNumber,
}
