use thiserror::Error;

/// A result.
pub type Result<T> = std::result::Result<T, Error>;

/// A lex result.
pub type LexResult<T> = std::result::Result<T, LexError>;

/// A parse result.
pub type ParseResult<T> = std::result::Result<T, ParseError>;

/// An assembler result
pub type AssemblerResult<T> = std::result::Result<T, AssemblerError>;

/// An error.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum Error {
  #[error("an error occurred during lexing")]
  Lexer(#[from] LexError),

  #[error("an error occurred during parsing")]
  Parser(#[from] ParseError),

  #[error("an error occurred during assembling")]
  Assembler(#[from] AssemblerError),
}
/// An error that occurred during lexing.
#[derive(Debug, Error, Copy, Clone, PartialEq, Eq)]
pub enum LexError {
  /// The lexer encountered invalid UTF-8.
  #[error("invalid utf-8 encountered at position `{0}`")]
  InvalidAscii(usize),

  #[error("expected the string to be closed at position `{0}`")]
  UnclosedString(usize),
}

/// An error that occurred during parsing.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error("parsing error occurred at {start_pos}: {kind}")]
pub struct ParseError {
  /// The position where the error ocurred.
  pub start_pos: usize,
  /// The error message.
  pub kind: ParserErrorKind,
}

/// The kind of error that occurred during parsing.
#[derive(Debug, Clone, Copy, Error, PartialEq, Eq)]
pub enum ParserErrorKind {
  #[error("the symbol is reserved")]
  ReservedSymbol,

  #[error("the length of the label name is invalid")]
  LabelNameSizeInvalid,

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

  #[error("expected linebreak")]
  ExpectedLinebreak,
}

/// An error that can occur during assembling.
#[derive(Debug, Copy, Clone, Error, PartialEq, Eq)]
pub enum AssemblerError {
  #[error("the label was already defined")]
  LabelRedefined,
}
