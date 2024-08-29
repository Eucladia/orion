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

  /// Advances the cursor
  fn advance(&mut self) {
    if !self.is_eof {
      self.curr += 1;
    }
  }

  /// Advances the cursor and returns that underlying byte
  fn next_byte(&mut self) -> Option<u8> {
    self.curr += 1;
    self.bytes.get(self.curr).map(|x| *x)
  }

  /// Lexes a [Token]
  fn lex_token(&mut self) -> Option<Token> {
    // SAFETY: This method isn't called directly and we check that the index is within bounds
    let byte = unsafe { self.current_byte().unwrap_unchecked() };
    let start = self.curr;

    // Use a lookup table that maps a byte to its type of token.
    // This is faster than traditional braching and checking for each condition.
    //
    // SAFETY: We have a byte and the lookup table has 256 entries
    let byte_type = unsafe { *BYTE_TOKEN_LOOKUP.get_unchecked(byte as usize) };

    match byte_type {
      ByteTokenType::WHITESPACE => {
        eat_whitespace(self);

        Some(create_token!(Whitespace, self.curr - start))
      }
      ByteTokenType::ALPHABETIC => {
        eat_identifier(self);

        let identifier = self
          .bytes
          .get(start..self.curr)
          .and_then(|bytes| std::str::from_utf8(bytes).ok())?;

        if Instruction::is_opcode(identifier) {
          Some(create_token!(Instruction, self.curr - start))
        } else if Register::is_register(identifier) {
          Some(create_token!(Register, self.curr - start))
        } else {
          Some(create_token!(Identifier, self.curr - start))
        }
      }
      ByteTokenType::NUMERIC => {
        eat_numerical_literal(self);

        // Check to see if there's a hex, octal, binary, or decimal suffix
        if matches!(
          self.current_byte(),
          Some(b'H' | b'h' | b'O' | b'o' | b'B' | b'b' | b'D' | b'd')
        ) {
          self.advance();
        }

        Some(create_token!(Literal, self.curr - start))
      }
      ByteTokenType::COMMENT => {
        eat_comment(self);

        Some(create_token!(Comment, self.curr - start))
      }
      ByteTokenType::COMMA => {
        self.advance();

        Some(create_token!(Comma, 1))
      }
      ByteTokenType::LABEL => {
        self.advance();

        Some(create_token!(Colon, 1))
      }
      ByteTokenType::INVALID => None,
    }
  }
}

// Eats a comment until it finds a linebreak
fn eat_comment(lexer: &mut Lexer) {
  while lexer
    .next_byte()
    .map_or(false, |b| b != b'\n' && b != b'\r')
  {}
}

// Eats a numerical literal. The suffix, if present is not included
fn eat_numerical_literal(lexer: &mut Lexer) {
  while lexer.next_byte().map_or(false, |b| b.is_ascii_digit()) {}
}

// Eats whitespace
fn eat_whitespace(lexer: &mut Lexer) {
  while lexer
    .next_byte()
    .map_or(false, |byte| byte.is_ascii_whitespace())
  {}
}

// Eats any kind of identifier
fn eat_identifier(lexer: &mut Lexer) {
  // The first character must be a letter, but the rest can include `_` and `.`
  while lexer
    .next_byte()
    .map_or(false, |b| b.is_ascii_alphabetic() || b == b'.' || b == b'_')
  {}
}

impl<'a> Iterator for Lexer<'a> {
  type Item = Token;

  fn next(&mut self) -> Option<Token> {
    if self.curr >= self.bytes.len() {
      if !self.is_eof {
        self.is_eof = true;

        return Some(create_token!(EndOfFile, 0));
      }

      return None;
    }

    self.lex_token()
  }
}

// Array where the index corresponds to the byte received by the Lexer.
//
// The value is the type of token for that byte.
const BYTE_TOKEN_LOOKUP: [ByteTokenType; 256] = {
  let mut default = [ByteTokenType::INVALID; 256];

  // Comma
  default[b',' as usize] = ByteTokenType::COMMA;
  // Whitespace characters, taken from `u8::is_ascii_whitespace`;
  default[b'\t' as usize] = ByteTokenType::WHITESPACE;
  default[b'\n' as usize] = ByteTokenType::WHITESPACE;
  default[b'\x0C' as usize] = ByteTokenType::WHITESPACE;
  default[b'\r' as usize] = ByteTokenType::WHITESPACE;
  default[b' ' as usize] = ByteTokenType::WHITESPACE;
  // Colon
  default[b':' as usize] = ByteTokenType::LABEL;
  // Comment
  default[b';' as usize] = ByteTokenType::COMMENT;

  // Numbers
  let mut i = b'0';

  while i <= b'9' {
    default[i as usize] = ByteTokenType::NUMERIC;
    i += 1;
  }

  // Alphabet
  i = b'a';

  while i <= b'z' {
    default[i as usize] = ByteTokenType::ALPHABETIC;
    i += 1;
  }

  i = b'A';

  while i <= b'Z' {
    default[i as usize] = ByteTokenType::ALPHABETIC;
    i += 1;
  }

  default
};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
enum ByteTokenType {
  COMMA,
  LABEL,
  COMMENT,
  NUMERIC,
  WHITESPACE,
  ALPHABETIC,
  INVALID,
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn empty_input() {
    let mut lexer = Lexer::from_str("");

    assert_eq!(lexer.next().unwrap(), create_token!(EndOfFile, 0));
  }
}
