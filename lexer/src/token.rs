#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Token {
  kind: TokenKind,
  len: usize,
}

impl Token {
  pub fn new(kind: TokenKind, len: usize) -> Self {
    Self { kind, len }
  }

  pub fn kind(&self) -> TokenKind {
    self.kind
  }

  pub fn length(&self) -> usize {
    self.len
  }
}

#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TokenKind {
  Whitespace,
  EndOfFile,
  Comment,
  Comma,
  Colon,
  Identifier,
  // I think the only literals are integers?
  Literal,
  // Separate these from `Identifier` to make life easier when parsing
  Instruction,
  Register,
}
