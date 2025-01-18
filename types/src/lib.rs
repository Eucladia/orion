use thiserror::Error;

/// A result.
pub type Result<T> = std::result::Result<T, Error>;

/// A lex result.
pub type LexResult<T> = std::result::Result<T, LexError>;

/// A parse result.
pub type ParseResult<T> = std::result::Result<T, ParseError>;

/// An assembler result
pub type AssembleResult<T> = std::result::Result<T, AssembleError>;

/// An error.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum Error {
  #[error("an error occurred during lexing")]
  Lexer(#[from] LexError),

  #[error("an error occurred during parsing")]
  Parser(#[from] ParseError),

  #[error("an error occurred during assembling")]
  Assembler(#[from] AssembleError),
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
#[error("parsing error occurred at {pos}: {kind}")]
pub struct ParseError {
  /// The starting position where the error ocurred.
  pub pos: usize,
  /// The error message.
  pub kind: ParseErrorKind,
}

/// The kind of error that occurred during parsing.
#[derive(Debug, Clone, Copy, Error, PartialEq, Eq)]
pub enum ParseErrorKind {
  #[error("the symbol is reserved")]
  ReservedIdentifier,

  #[error("the length of the label name is invalid")]
  InvalidLabelLength,

  #[error("the length of the string is invalid")]
  InvalidStringLength,

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
#[error("assemble error occurred at {pos}: {kind}")]
pub struct AssembleError {
  pub pos: usize,
  pub kind: AssembleErrorKind,
}

/// The kind of assemble error.
#[derive(Debug, Copy, Clone, Error, PartialEq, Eq)]
pub enum AssembleErrorKind {
  #[error("an invalid operand type was passed")]
  InvalidOperandType,

  #[error("an invalid operand value was passed")]
  InvalidOperandValue,

  #[error("the value was not 2 bytes")]
  ExpectedTwoByteValue,

  #[error("the value was not 1 byte")]
  ExpectedOneByteValue,

  #[error("the label was already defined")]
  LabelRedefined,

  #[error("the identifier was not defined yet")]
  IdentifierNotDefined,
}

impl AssembleError {
  pub fn new(starting_pos: usize, kind: AssembleErrorKind) -> Self {
    Self {
      pos: starting_pos,
      kind,
    }
  }
}

impl ParseError {
  pub fn new(starting_pos: usize, kind: ParseErrorKind) -> Self {
    Self {
      pos: starting_pos,
      kind,
    }
  }
}
