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
  // Do I want to include comments?
  Comment,
  Comma,
  Identifier,
  // I think the only literals are integers?
  Literal,
  // Separate these from `Literal` to make life easier when parsing
  Instruction,
  Register,
}
