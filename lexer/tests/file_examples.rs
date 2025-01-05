use lexer::{lex, token::TokenKind, Token};

macro_rules! tokens_equal {
  ($src:literal, $($token:tt),*) => {
    let tokens = lex(include_str!(concat!("../../test_files/", $src, ".asm")))
      .map(|toks| toks.iter().map(Token::kind).collect());
    let expected = vec![$(TokenKind::$token),*];

    assert_eq!(tokens, Ok(expected));
  };
}

#[test]
fn ones_complement() {
  #[rustfmt::skip]
  tokens_equal!(
    "ones_complement",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn twos_compliment() {
  #[rustfmt::skip]
  tokens_equal!(
    "twos_complement",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn add_two_bytes() {
  #[rustfmt::skip]
   tokens_equal!(
    "add_two_bytes",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn num_zeros_in_byte() {
  #[rustfmt::skip]
  tokens_equal!(
    "num_zeros_in_byte",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn occurrences_of_number() {
  #[rustfmt::skip]
  tokens_equal!(
    "occurrences_of_num",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Numeric, Whitespace, Comment, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn max_array_value() {
  #[rustfmt::skip]
  tokens_equal!(
    "max_array_value",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn min_num_in_n_array() {
  #[rustfmt::skip]
  tokens_equal!(
    "min_num_in_n_array",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn even_numbers_in_array() {
  #[rustfmt::skip]
  tokens_equal!(
    "even_numbers_in_array",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Whitespace, Comment, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Whitespace, Comment, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Whitespace, Comment, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}

#[test]
fn pos_or_neg() {
  #[rustfmt::skip]
  tokens_equal!(
    "pos_or_neg",
    Comment, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Identifier, Colon, Whitespace, Instruction,
    EndOfFile
  );
}

#[test]
fn sum_of_array() {
  #[rustfmt::skip]
  tokens_equal!(
    "sum_of_array",
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Whitespace, Comment, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Numeric, Whitespace, Comment, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Register, Whitespace, Comment, Linebreak,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Identifier, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Linebreak,
    Instruction, Whitespace, Numeric, Linebreak,
    Instruction,
    EndOfFile
  );
}
