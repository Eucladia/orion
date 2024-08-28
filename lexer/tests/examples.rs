use lexer::{Lexer, TokenKind};

macro_rules! create_tokens {
  ($($token:tt),*) => {
    vec![$(TokenKind::$token),*]
  };
}

#[test]
fn ones_complement() {
  let lexer = Lexer::from_bytes(include_bytes!("files/ones_complement.asm"));

  let tokens = lexer.into_iter().map(|tok| tok.kind()).collect::<Vec<_>>();

  #[rustfmt::skip]
  let expected = create_tokens!(
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );

  assert_eq!(tokens, expected);
}

#[test]
fn twos_compliment() {
  let lexer = Lexer::from_bytes(include_bytes!("files/twos_complement.asm"));

  let tokens = lexer.into_iter().map(|tok| tok.kind()).collect::<Vec<_>>();

  #[rustfmt::skip]
  let expected = create_tokens!(
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );

  assert_eq!(tokens, expected);
}

#[test]
fn add_two_bytes() {
  let lexer = Lexer::from_bytes(include_bytes!("files/add_two_bytes.asm"));

  let tokens = lexer.into_iter().map(|tok| tok.kind()).collect::<Vec<_>>();

  #[rustfmt::skip]
  let expected = create_tokens!(
    Instruction, Whitespace, Register, Comma, Whitespace, Literal, Whitespace,
    Instruction, Whitespace, Register, Comma, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Register, Whitespace,
    Instruction, Whitespace, Literal, Whitespace,
    Instruction,
    EndOfFile
  );

  assert_eq!(tokens, expected);
}
