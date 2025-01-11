use std::ops::Range;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Token {
  kind: TokenKind,
  range: Range<usize>,
}

impl Token {
  /// Creates a new [`Token`] with the given [`TokenKind`] and length.
  pub fn new(kind: TokenKind, range: Range<usize>) -> Self {
    Self { kind, range }
  }

  /// Returns the [`TokenKind`] of this token.
  pub fn kind(&self) -> TokenKind {
    self.kind
  }

  /// Returns the range of this token.
  pub fn span(&self) -> Range<usize> {
    self.range.clone()
  }
}

#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TokenKind {
  /// The following whitespace characters: `\t`, ` `, and `\xOC`.
  Whitespace,
  /// Linebreak characters: `\n` & `\r`
  Linebreak,
  /// A token representing a token.
  ///
  /// Note that the token's span includes the single quotes.
  String,
  /// The end of the input source.
  EndOfFile,
  /// The comment character, `;`.
  Comment,
  /// The comma character, `,`.
  Comma,
  /// The colon character, `:`.
  Colon,
  /// A numeric literal.
  ///
  /// Numeric literals may end in a `B`, `D, `Q`, `O` or `H` suffix.
  Numeric,
  /// An identifier.
  ///
  /// Identifiers MUST start with a letter, but can be followed with a number, `$`, or `_`.
  Identifier,
  // Separate these 2 from `Identifier` to make life easier when parsing
  /// An 8085 assembly instruction.
  Instruction,
  /// A register.
  ///
  /// The registers are `A`, `B`, `C`, `D`, `E`, `H`, `L`, and a psuedo-register `M`.
  Register,
  /// An operator.
  ///
  /// These include arithmetical operators - `+`, `-`, `*`, `/`, `MOD`, `SHR`, and `SHL`.
  /// It also includs logical operators -  `NOT`, `AND`,`OR`, `XOR`, `EQ`, `NE`, `LT`,
  // `LE`, `GT`, and `GE`.
  ///
  /// Arithmetic operators are evaluated by the assembler and then hardcoded.
  Operator,
  /// A left parenthesis, `(`.
  LeftParenthesis,
  /// A right parenthesis, `)`.
  RightParenthesis,
  /// An unknown token.
  ///
  /// This is just here for the purposes of being loseless.
  Unknown,
}

impl std::fmt::Display for TokenKind {
  fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(fmt, "{:?}", self)
  }
}
