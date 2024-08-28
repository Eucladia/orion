use crate::{create_token, instruction::Instruction, register::Register, token::Token};

pub struct Lexer<'a> {
  curr: usize,
  bytes: &'a [u8],
  is_eof: bool,
}

impl<'a> Lexer<'a> {
  /// Creates a [Lexer] from a slice of bytes
  pub fn from_bytes(bytes: &'a [u8]) -> Self {
    Self {
      bytes,
      curr: 0,
      is_eof: false,
    }
  }

  /// Creates a [Lexer] from a a [str]
  pub fn from_str(content: &'a str) -> Self {
    Self {
      bytes: content.as_bytes(),
      curr: 0,
      is_eof: false,
    }
  }

  /// Returns the current index
  pub fn index(&self) -> usize {
    self.curr
  }

  // Returns the current byte
  pub fn current_byte(&self) -> Option<u8> {
    self.bytes.get(self.curr).map(|x| *x)
  }

  /// Lexes a [Token]
  pub fn lex_token(&mut self) -> Option<Token> {
    if self.is_eof {
      return None;
    }

    let byte = self.bytes.get(self.curr);

    if byte.is_none() {
      self.is_eof = true;

      return Some(create_token!(EndOfFile, 0));
    }

    let byte = *byte.unwrap();
    let start = self.curr;

    if byte.is_ascii_whitespace() {
      eat_whitespace(self);

      Some(create_token!(Whitespace, self.curr - start))
    } else if byte.is_ascii_alphabetic() {
      eat_identifier(self);

      let string = self
        .bytes
        .get(start..self.curr)
        .and_then(|bytes| std::str::from_utf8(bytes).ok())?;

      if Instruction::is_opcode(string) {
        Some(create_token!(Instruction, self.curr - start))
      } else if Register::is_register(string) {
        Some(create_token!(Register, self.curr - start))
      } else {
        Some(create_token!(Identifier, self.curr - start))
      }
    } else if byte.is_ascii_digit() {
      eat_numerical_literal(self);

      // Check to see if there's a hex, octal, binary, or decimal suffix
      if matches!(
        self.current_byte(),
        Some(b'H')
          | Some(b'h')
          | Some(b'O')
          | Some(b'o')
          | Some(b'B')
          | Some(b'b')
          | Some(b'D')
          | Some(b'd')
      ) {
        self.advance();
      }

      Some(create_token!(Literal, self.curr - start))
    } else if byte == b',' {
      self.advance();
      Some(create_token!(Comma, 1))
    } else {
      None
    }
  }

  /// Advances the cursor
  fn advance(&mut self) {
    if !self.is_eof {
      self.curr += 1;
    }
  }

  /// Advances the cursor and returns that underlying byte
  fn next(&mut self) -> Option<u8> {
    self.curr += 1;
    self.bytes.get(self.curr).map(|x| *x)
  }
}

// Eats a numerical literal. The suffix, if present is not included
fn eat_numerical_literal(lexer: &mut Lexer) {
  while lexer.next().map_or(false, |b| b.is_ascii_digit()) {}
}

// Eats whitespace
fn eat_whitespace(lexer: &mut Lexer) {
  while lexer
    .next()
    .map_or(false, |byte| byte.is_ascii_whitespace())
  {}
}

// Eats any kind of identifier
fn eat_identifier(lexer: &mut Lexer) {
  // The first character must be a letter, but the rest can include `_` and `.`
  while lexer
    .next()
    .map_or(false, |b| b.is_ascii_alphabetic() || b == b'.' || b == b'_')
  {}
}

impl<'a> Iterator for Lexer<'a> {
  type Item = Token;

  fn next(&mut self) -> Option<Token> {
    if self.is_eof {
      return None;
    }

    self.lex_token()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn empty_input() {
    let mut lexer = Lexer::from_str("");

    assert_eq!(lexer.lex_token().unwrap(), create_token!(EndOfFile, 0));
  }
}
