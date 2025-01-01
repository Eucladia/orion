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
  /// Any whitespace characters – `\n` & `\r`, `\t`, ` `, and `\xOC`.
  Whitespace,
  /// The end of the input source.
  EndOfFile,
  /// The comment character, `;`.
  Comment,
  /// The comma character, `,`.
  Comma,
  /// The colon character, `:`.
  Colon,
  /// The only literals in 8085 assembly are integers.
  Literal,
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
