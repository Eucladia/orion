use lexer::{token::TokenKind, LexResult, Lexer};

macro_rules! tokens_equal {
  ($src:literal, $($token:tt),*) => {
    let lexer = Lexer::from_bytes(include_bytes!(concat!("../../test_files/", $src, ".asm")));
    let tokens = lexer.into_iter().map(|res| res.map(|tok| tok.kind())).collect::<LexResult<Vec<_>>>();
    let expected = vec![$(TokenKind::$token),*];


    assert_eq!(tokens, Ok(expected));
  };
}

#[test]
fn ones_complement() {
  #[rustfmt::skip]
  tokens_equal!(
    "ones_complement",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn twos_compliment() {
  #[rustfmt::skip]
  tokens_equal!(
    "twos_complement",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn add_two_bytes() {
  #[rustfmt::skip]
   tokens_equal!(
    "add_two_bytes",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn num_zeros_in_byte() {
  #[rustfmt::skip]
  tokens_equal!(
    "num_zeros_in_byte",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn occurrences_of_number() {
  #[rustfmt::skip]
  tokens_equal!(
    "occurrences_of_num",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Literal, Whitespace, Comment, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn max_array_value() {
  #[rustfmt::skip]
  tokens_equal!(
    "max_array_value",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn min_num_in_n_array() {
  #[rustfmt::skip]
  tokens_equal!(
    "min_num_in_n_array",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn even_numbers_in_array() {
  #[rustfmt::skip]
  tokens_equal!(
    "even_numbers_in_array",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace, Comment, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace, Comment, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace, Comment, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}

#[test]
fn pos_or_neg() {
  #[rustfmt::skip]
  tokens_equal!(
    "pos_or_neg",
    Comment, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Identifier, Colon, Whitespace, Instruction,
    EndOfFile
  );
}

#[test]
fn sum_of_array() {
  #[rustfmt::skip]
  tokens_equal!(
    "sum_of_array",
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace, Comment, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace, Comment, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Register, Whitespace, Comment, Whitespace,
    Identifier, Colon, Whitespace, Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Identifier, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );
}
