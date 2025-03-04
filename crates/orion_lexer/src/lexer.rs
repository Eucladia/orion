use crate::{
  create_token, directive::Directive, instruction::Instruction, register::Register, token::Token,
};
use orion_types::{LexError, LexResult};

// A lexer used to lex a source program into tokens.
pub struct Lexer<'a> {
  curr: usize,
  bytes: &'a [u8],
  is_eof: bool,
}

impl<'a> Lexer<'a> {
  /// Creates a [`Lexer`] from a slice of bytes
  pub fn from_bytes(bytes: &'a [u8]) -> Self {
    Self {
      bytes,
      curr: 0,
      is_eof: false,
    }
  }

  /// Creates a [`Lexer`] from a a [str]
  pub fn from_string(content: &'a str) -> Self {
    Self {
      bytes: content.as_bytes(),
      curr: 0,
      is_eof: false,
    }
  }

  /// Returns the current byte.
  fn current_byte(&self) -> Option<u8> {
    self.bytes.get(self.curr).copied()
  }

  /// Advances the cursor.
  fn advance(&mut self) {
    if self.curr < self.bytes.len() {
      self.curr += 1;
    }
  }

  /// Advances the cursor and returns that underlying byte.
  fn next_byte(&mut self) -> Option<u8> {
    self.curr += 1;
    self.bytes.get(self.curr).copied()
  }

  /// Lexes a [`Token`].
  fn lex_token(&mut self) -> Option<LexResult<Token>> {
    // SAFETY: This method is private and only gets called in the `Iterator `interface,
    // which we bounds check.
    let byte = unsafe { self.current_byte().unwrap_unchecked() };
    let start = self.curr;

    // Use a lookup table that maps a byte to its type of token.
    //
    // This is faster than traditional braching and checking if the byte
    // is a certain token kind.
    //
    // SAFETY: We have a byte and the lookup table has 256 entries
    let byte_type = unsafe { *BYTE_TOKEN_LOOKUP.get_unchecked(byte as usize) };

    match byte_type {
      ByteTokenType::WHITESPACE => {
        eat_whitespace(self);

        Some(Ok(create_token!(Whitespace, start..self.curr)))
      }
      ByteTokenType::LEFT_PAREN => {
        self.advance();

        Some(Ok(create_token!(LeftParenthesis, start..self.curr)))
      }
      ByteTokenType::RIGHT_PAREN => {
        self.advance();

        Some(Ok(create_token!(RightParenthesis, start..self.curr)))
      }
      ByteTokenType::PLUS | ByteTokenType::MINUS | ByteTokenType::STAR | ByteTokenType::SLASH => {
        self.advance();

        Some(Ok(create_token!(Operator, start..self.curr)))
      }
      ByteTokenType::LINEBREAK => {
        self.advance();

        Some(Ok(create_token!(Linebreak, start..self.curr)))
      }
      ByteTokenType::QUOTE => {
        if let Err(e) = eat_string(self) {
          return Some(Err(e));
        }

        Some(Ok(create_token!(String, start..self.curr)))
      }
      ByteTokenType::ALPHABETIC => {
        eat_identifier(self);

        let span = start..self.curr;
        // SAFETY: We know the range is valid and we only consume valid ASCII.
        let identifier =
          unsafe { std::str::from_utf8_unchecked(self.bytes.get_unchecked(span.clone())) };

        if Instruction::is_opcode(identifier) {
          Some(Ok(create_token!(Instruction, span)))
        } else if Register::is_register(identifier) {
          Some(Ok(create_token!(Register, span)))
        } else if Directive::is_directive(identifier) {
          Some(Ok(create_token!(Directive, span)))
        } else if is_operator(identifier) {
          Some(Ok(create_token!(Operator, span)))
        } else {
          // NOTE: This includes `$`, which aren't valid identifiers.
          Some(Ok(create_token!(Identifier, span)))
        }
      }
      ByteTokenType::NUMERIC => {
        eat_numerical_literal(self);

        Some(Ok(create_token!(Numeric, start..self.curr)))
      }
      ByteTokenType::COMMENT => {
        eat_comment(self);

        Some(Ok(create_token!(Comment, start..self.curr)))
      }
      ByteTokenType::COMMA => {
        self.advance();

        Some(Ok(create_token!(Comma, start..start + 1)))
      }
      ByteTokenType::COLON => {
        self.advance();

        Some(Ok(create_token!(Colon, start..start + 1)))
      }
      ByteTokenType::INVALID => {
        self.advance();

        Some(Ok(create_token!(Unknown, start..start + 1)))
      }
    }
  }
}

fn eat_string(lexer: &mut Lexer) -> LexResult<()> {
  loop {
    let byte = lexer.next_byte();

    match byte {
      Some(b'\n' | b'\r') | None => return Err(LexError::UnclosedString(lexer.curr)),
      Some(x) if !x.is_ascii() => return Err(LexError::InvalidAscii(lexer.curr)),
      // Strings are escaped via 2 single quotes
      Some(b'\'') => match lexer.next_byte() {
        // Keep consuming since it's a valid escaped string
        Some(b'\'') => continue,
        // Any other character means that the string was closed
        Some(_) | None => break,
      },
      // Keep consuming if we get valid ASCII
      Some(_) => continue,
    }
  }

  Ok(())
}

// Eats a comment until it finds a linebreak
fn eat_comment(lexer: &mut Lexer) {
  while lexer.next_byte().is_some_and(|b| b != b'\n' && b != b'\r') {}
}

// Eats a potential numerical literal, without checking for the validity of the number.
fn eat_numerical_literal(lexer: &mut Lexer) {
  while lexer.next_byte().is_some_and(|b| {
    let b = b.to_ascii_lowercase();

    // Check if it's a number or a hex number or valid numeric suffix
    // Valid suffixes include b, d, h, o, and q
    b.is_ascii_digit()
      || b == b'a'
      || b == b'b'
      || b == b'c'
      || b == b'd'
      || b == b'e'
      || b == b'f'
      || b == b'h'
      || b == b'o'
      || b == b'q'
  }) {}
}

// Eats whitespace
fn eat_whitespace(lexer: &mut Lexer) {
  while lexer
    .next_byte()
    .is_some_and(|b| b.is_ascii_whitespace() && b != b'\n' && b != b'\r')
  {}
}

// Eats any kind of identifier
fn eat_identifier(lexer: &mut Lexer) {
  // A label's first character must be alphabetic (including `?` and `@`),
  // but the rest can be alphanumeric or `?`
  while lexer
    .next_byte()
    .is_some_and(|b| b.is_ascii_alphanumeric() || b == b'?')
  {}
}

fn is_operator(identifier: &str) -> bool {
  // Arithmetic
  identifier.eq_ignore_ascii_case("mod")
    // Bitwise ops
    || identifier.eq_ignore_ascii_case("shl")
    || identifier.eq_ignore_ascii_case("shr")
    || identifier.eq_ignore_ascii_case("not")
    || identifier.eq_ignore_ascii_case("and")
    || identifier.eq_ignore_ascii_case("or")
    || identifier.eq_ignore_ascii_case("xor")
    // Equality
    || identifier.eq_ignore_ascii_case("eq")
    || identifier.eq_ignore_ascii_case("ne")
    || identifier.eq_ignore_ascii_case("lt")
    || identifier.eq_ignore_ascii_case("le")
    || identifier.eq_ignore_ascii_case("gt")
    || identifier.eq_ignore_ascii_case("ge")
}

impl Iterator for Lexer<'_> {
  type Item = LexResult<Token>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.curr >= self.bytes.len() {
      if !self.is_eof {
        self.is_eof = true;

        return Some(Ok(create_token!(EndOfFile, self.curr..self.curr)));
      }

      return None;
    }

    self.lex_token()
  }
}

/// Creates a [`Token`] with the following [`TokenKind`] and length
///
/// [`TokenKind`]: crate::token::TokenKind
#[macro_export]
macro_rules! create_token {
  ($token:tt, $range:expr) => {
    $crate::token::Token::new($crate::token::TokenKind::$token, $range)
  };
}

#[allow(clippy::upper_case_acronyms, non_camel_case_types)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
enum ByteTokenType {
  COMMA,
  COLON,
  COMMENT,
  NUMERIC,
  LINEBREAK,
  WHITESPACE,
  ALPHABETIC,
  QUOTE,
  PLUS,
  MINUS,
  STAR,
  SLASH,
  RIGHT_PAREN,
  LEFT_PAREN,
  INVALID,
}

// Array where the index corresponds to the byte received by the Lexer.
//
// The value is the type of token for that byte.
const BYTE_TOKEN_LOOKUP: [ByteTokenType; 256] = {
  let mut default = [ByteTokenType::INVALID; 256];

  // Comma
  default[b',' as usize] = ByteTokenType::COMMA;
  // Whitespace characters, taken from `u8::is_ascii_whitespace`
  default[b'\t' as usize] = ByteTokenType::WHITESPACE;
  default[b'\x0C' as usize] = ByteTokenType::WHITESPACE;
  default[b' ' as usize] = ByteTokenType::WHITESPACE;
  // Linebreak characters
  default[b'\n' as usize] = ByteTokenType::LINEBREAK;
  default[b'\r' as usize] = ByteTokenType::LINEBREAK;
  // Colon
  default[b':' as usize] = ByteTokenType::COLON;
  // Comment
  default[b';' as usize] = ByteTokenType::COMMENT;
  // Quote
  default[b'\'' as usize] = ByteTokenType::QUOTE;
  // Parenthesis
  default[b'(' as usize] = ByteTokenType::LEFT_PAREN;
  default[b')' as usize] = ByteTokenType::RIGHT_PAREN;

  // Arithmetic operators
  default[b'+' as usize] = ByteTokenType::PLUS;
  default[b'-' as usize] = ByteTokenType::MINUS;
  default[b'*' as usize] = ByteTokenType::STAR;
  default[b'/' as usize] = ByteTokenType::SLASH;

  // Numbers
  let mut i = b'0';

  while i <= b'9' {
    default[i as usize] = ByteTokenType::NUMERIC;
    i += 1;
  }

  // Alphabetical
  default[b'?' as usize] = ByteTokenType::ALPHABETIC;
  default[b'@' as usize] = ByteTokenType::ALPHABETIC;
  // Reserved character, `$` is for the program counter
  default[b'$' as usize] = ByteTokenType::ALPHABETIC;

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

#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! get_tokens {
    ($src:expr) => {{
      let tokens = crate::lex($src).map(|mut toks| {
        toks.pop();
        toks
      });

      tokens
    }};
  }

  #[test]
  fn strings() {
    assert_eq!(
      get_tokens!("MVI A, 'F'"),
      Ok(vec![
        create_token!(Instruction, 0..3),
        create_token!(Whitespace, 3..4),
        create_token!(Register, 4..5),
        create_token!(Comma, 5..6),
        create_token!(Whitespace, 6..7),
        create_token!(String, 7..10)
      ]),
      "expected ok for single char string"
    );

    assert_eq!(
      // Technically this is invalid because we can only have 1 byte, but this will
      // get parsed in the parser
      get_tokens!("MVI A, 'FOO'"),
      Ok(vec![
        create_token!(Instruction, 0..3),
        create_token!(Whitespace, 3..4),
        create_token!(Register, 4..5),
        create_token!(Comma, 5..6),
        create_token!(Whitespace, 6..7),
        create_token!(String, 7..12)
      ]),
      "expected ok for multi char string"
    );

    assert_eq!(
      get_tokens!("MVI A, 'F"),
      Err(LexError::UnclosedString(9)),
      "expected error for unclosed single char string"
    );

    assert_eq!(
      get_tokens!("MVI A, 'FOO"),
      Err(LexError::UnclosedString(11)),
      "expected error for unclosed multi char string"
    );

    assert_eq!(
      get_tokens!("MVI A, 'FOO''S BAR"),
      Err(LexError::UnclosedString(18)),
      "expected error for unclosed multi char escaped string"
    );

    assert_eq!(
      get_tokens!("MVI A, 'FOO''S BAR'"),
      Ok(vec![
        create_token!(Instruction, 0..3),
        create_token!(Whitespace, 3..4),
        create_token!(Register, 4..5),
        create_token!(Comma, 5..6),
        create_token!(Whitespace, 6..7),
        create_token!(String, 7..19)
      ]),
      "expected ok for multi char escaped string"
    );

    assert_eq!(
      get_tokens!("MVI A, 'FOO''S BAR'\nHLT"),
      Ok(vec![
        create_token!(Instruction, 0..3),
        create_token!(Whitespace, 3..4),
        create_token!(Register, 4..5),
        create_token!(Comma, 5..6),
        create_token!(Whitespace, 6..7),
        create_token!(String, 7..19),
        create_token!(Linebreak, 19..20),
        create_token!(Instruction, 20..23)
      ]),
      "expected ok for multi instruction, multi char escaped string"
    );

    assert_eq!(
      get_tokens!("MVI A, 'FOO''S BAR\nHLT"),
      Err(LexError::UnclosedString(18)),
      "expected error for multi instruction, multi char escaped string"
    );
  }

  #[test]
  fn empty_input() {
    assert_eq!(get_tokens!(""), Ok(vec![]));
  }

  #[test]
  fn gibberish() {
    assert_eq!(
      get_tokens!("`~~~_="),
      Ok(vec![
        create_token!(Unknown, 0..1),
        create_token!(Unknown, 1..2),
        create_token!(Unknown, 2..3),
        create_token!(Unknown, 3..4),
        create_token!(Unknown, 4..5),
        create_token!(Unknown, 5..6),
      ])
    )
  }

  #[test]
  fn loseless() {
    // Check to see if we can reconstruct a program from its tokens
    let string = include_str!("../../../test_files/sum_of_array.asm");
    let tokens = get_tokens!(string).unwrap();
    let mut new_string = String::with_capacity(string.len());

    for token in tokens.into_iter() {
      new_string.push_str(string.get(token.span()).unwrap());
    }

    assert_eq!(string, new_string);
  }
}
