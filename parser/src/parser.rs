use crate::nodes::{InstructionNode, LabelNode, Node, OperandNode, ProgramNode};
use crate::unwrap;

use lexer::instruction::Instruction;
use lexer::token::{Token, TokenKind};
use lexer::Register;
use types::{LexResult, ParseError, ParseResult, ParserErrorKind};

use smol_str::{SmolStr, SmolStrBuilder};

use std::num::IntErrorKind;
use std::ops::Range;

/// The maximum length of a label name.
pub const MAX_LABEL_NAME: usize = 6;

pub struct Parser<'a> {
  source: &'a str,
  tokens: Vec<Token>,
  token_index: usize,
}

impl<'a> Parser<'a> {
  pub fn new(source: &'a str, tokens: Vec<Token>) -> Self {
    Self {
      source,
      tokens,
      token_index: 0,
    }
  }

  pub fn from_source(source: &'a str) -> LexResult<Self> {
    Ok(Self {
      source,
      tokens: lexer::lex(source)?,
      token_index: 0,
    })
  }

  /// Gets a [`str`] from the selected range.
  pub fn get_source_content(&self, range: Range<usize>) -> Option<&str> {
    self.source.get(range)
  }

  pub fn parse(&mut self) -> ParseResult<ProgramNode> {
    let mut nodes = Vec::new();

    while let Some(node) = self.parse_next() {
      nodes.push(node?);
    }

    Ok(ProgramNode::new(nodes))
  }

  pub fn parse_next(&mut self) -> Option<ParseResult<Node>> {
    let token = self.next_non_whitespace_token()?;

    match token.kind() {
      TokenKind::Identifier => {
        let ident = unwrap!(self.get_source_content(token.span()));

        if ident.starts_with("$") && ident.len() > 1 {
          return Some(Err(ParseError {
            start_pos: token.span().start,
            kind: ParserErrorKind::ReservedSymbol,
          }));
        }

        let label_node = self.try_parse_label(&token);

        if let Some(node) = label_node {
          if node.label_name().len() > MAX_LABEL_NAME {
            Some(Err(ParseError {
              start_pos: token.span().start,
              kind: ParserErrorKind::LabelNameSizeInvalid,
            }))
          } else {
            Some(Ok(Node::Label(node)))
          }
        } else {
          // TODO: Parse directives here
          todo!("other non label idents")
        }
      }
      TokenKind::Instruction => {
        let instruction_node = self.parse_instruction(&token);

        Some(match instruction_node {
          Ok(node) => Ok(Node::Instruction(node)),
          Err(e) => Err(e),
        })
      }

      TokenKind::EndOfFile => None,

      _ => Some(Err(ParseError {
        start_pos: token.span().start,
        kind: ParserErrorKind::UnexpectedToken,
      })),
    }
  }

  fn try_parse_label(&mut self, ident_token: &Token) -> Option<LabelNode> {
    let next_token = self.next_non_whitespace_token();

    match next_token {
      Some(colon_token) if matches!(colon_token.kind(), TokenKind::Colon) => {
        // SAFETY: We have a valid identifier token and we just checked for a colon, given
        // the immutable source str
        let label_name = unwrap!(self.get_source_content(ident_token.span())).to_string();

        Some(LabelNode::new(SmolStr::new(&label_name)))
      }
      _ => None,
    }
  }

  fn parse_instruction(&mut self, instruction_token: &Token) -> ParseResult<InstructionNode> {
    // SAFETY: We have an immutable str and the lexer produced this `Instruction` token,
    // so this str is still valid
    let instruction_str = unwrap!(self.get_source_content(instruction_token.span()));
    let instruction = unwrap!(Instruction::from_string(instruction_str));

    let num_operands = instruction.num_operands();
    let mut operands = Vec::with_capacity(num_operands);
    let mut last_token_operand = false;
    let mut last_token = instruction_token.clone();

    while operands.len() < num_operands {
      match self.next_non_whitespace_token() {
        Some(token) if matches!(token.kind(), TokenKind::Register) => {
          // SAFETY: We have a valid `Register` token produced from the lexer and an immutable str
          let reg_str = unwrap!(self.get_source_content(token.span()));
          let reg = unwrap!(Register::from_string(reg_str));

          operands.push(OperandNode::Register(reg));
          last_token_operand = true;
          last_token = token;
        }
        Some(token) if matches!(token.kind(), TokenKind::Literal) => {
          // SAFETY: We have a valid `Literal` token produced from the lexer and an immutable str
          let mut num_str = unwrap!(self.get_source_content(token.span()));
          // SAFETY: We're guaranteed at least one byte for `Literal`s.
          let last_byte = unwrap!(num_str.as_bytes().last().copied());
          let mut base = None;

          if matches!(last_byte, b'H' | b'O' | b'Q' | b'B' | b'D') {
            // SAFETY: We have at least one byte in this token
            num_str = unwrap!(num_str.get(..num_str.len() - 1));
            base = Some(last_byte);
          }

          let number = parse_number(num_str, base, token.span())?;

          operands.push(OperandNode::Literal(number));
          last_token_operand = true;
          last_token = token;
        }
        Some(token) if matches!(token.kind(), TokenKind::Identifier) => {
          // SAFETY: We have a valid `Identifier` token produced by the lexer and an immutable str
          let ident = unwrap!(self.get_source_content(token.span()));

          operands.push(OperandNode::Identifier(SmolStr::new(ident)));
          last_token_operand = true;
          last_token = token;
        }
        Some(token) if matches!(token.kind(), TokenKind::String) => {
          let parsed_str = parse_string(self.source.as_bytes(), token.span());

          operands.push(OperandNode::String(parsed_str));
          last_token_operand = true;
          last_token = token;
        }
        Some(token) if matches!(token.kind(), TokenKind::Comma) => {
          if !last_token_operand {
            return Err(ParseError {
              start_pos: token.span().start,
              kind: ParserErrorKind::UnexpectedToken,
            });
          }

          last_token_operand = false;
        }
        Some(token) => {
          return Err(ParseError {
            start_pos: token.span().start,
            kind: ParserErrorKind::InvalidOperand,
          });
        }
        None => {
          return Err(ParseError {
            start_pos: self.source.len(),
            kind: ParserErrorKind::ExpectedOperand,
          });
        }
      }
    }

    // Make sure the next non-comment token, if any, is a linebreak
    let next_token = self.next_token();

    if !matches!(
      next_token.as_ref().map(Token::kind),
      Some(TokenKind::EndOfFile | TokenKind::Linebreak) | None
    ) {
      return Err(ParseError {
        // Point to the end of the last token
        start_pos: last_token.span().end,
        kind: ParserErrorKind::ExpectedLinebreak,
      });
    }

    // Check if the types to the instruction are valid
    if instruction_type_error(&instruction, &operands) {
      Err(ParseError {
        // Point to the start of the instruction that has the error
        start_pos: instruction_token.span().start,
        kind: ParserErrorKind::InvalidOperandType,
      })
    } else {
      Ok(InstructionNode::from_operands(instruction, operands))
    }
  }

  /// Gets the next token that isn't whitespace or a comment.
  fn next_token(&mut self) -> Option<Token> {
    loop {
      let token = self.tokens.get(self.token_index)?;

      self.token_index += 1;

      if !matches!(token.kind(), TokenKind::Whitespace | TokenKind::Comment) {
        return Some(token.clone());
      }
    }
  }

  /// Gets the enxt token that isn't whitespace, a linebreak, or a comment.
  fn next_non_whitespace_token(&mut self) -> Option<Token> {
    loop {
      let token = self.tokens.get(self.token_index)?;

      self.token_index += 1;

      if !matches!(
        token.kind(),
        TokenKind::Whitespace | TokenKind::Linebreak | TokenKind::Comment
      ) {
        return Some(token.clone());
      }
    }
  }
}

fn parse_string(source_bytes: &[u8], span: Range<usize>) -> SmolStr {
  let mut str = SmolStrBuilder::new();
  let contents = source_bytes.get(span.start + 1..span.end - 1).unwrap();
  let mut escaped_quote = false;

  for &byte in contents.iter() {
    if byte == b'\'' {
      // If we had a `'` before, then we should insert this `'`.
      if escaped_quote {
        str.push(byte as char);
      }

      escaped_quote = !escaped_quote;
    } else {
      str.push(byte as char);
    }
  }

  str.finish()
}

fn instruction_type_error(instruction: &Instruction, ops: &[OperandNode]) -> bool {
  use Instruction::*;

  match (instruction, ops) {
    // Register-Register operands
    (MOV, &[OperandNode::Register(_), OperandNode::Register(_)]) => false,

    // Register-d16 operands
    (
      LXI,
      &[OperandNode::Register(Register::B | Register::D | Register::H | Register::SP), OperandNode::Literal(_)],
    ) => false,

    // Register-d8 operands
    (
      MVI,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      ), OperandNode::Literal(x)],
    ) if x <= u8::MAX as u16 => false,
    (
      MVI,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      ), OperandNode::String(ref x)],
      // MVI can only take a d8, so we only want 1 ASCII character
    ) if x.len() == 1 => false,

    // Register operands
    (STAX, &[OperandNode::Register(Register::B | Register::D)]) => false,
    (INX, &[OperandNode::Register(Register::B | Register::D | Register::H | Register::SP)]) => {
      false
    }
    (INR, &[OperandNode::Register(Register::B | Register::D | Register::H | Register::M)]) => false,
    (DCR, &[OperandNode::Register(Register::B | Register::D | Register::H | Register::M)]) => false,
    (DAD, &[OperandNode::Register(Register::B | Register::D | Register::H | Register::SP)]) => {
      false
    }
    (LDAX, &[OperandNode::Register(Register::B | Register::D)]) => false,
    (INR, &[OperandNode::Register(Register::C | Register::E | Register::L | Register::A)]) => false,
    (DCR, &[OperandNode::Register(Register::C | Register::E | Register::L | Register::A)]) => false,
    (DCX, &[OperandNode::Register(Register::B | Register::D | Register::H | Register::SP)]) => {
      false
    }
    (
      ADD,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (
      ADC,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (
      SUB,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (
      SBB,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (
      ANA,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (
      XRA,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (
      ORA,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (
      CMP,
      &[OperandNode::Register(
        Register::A
        | Register::B
        | Register::C
        | Register::D
        | Register::E
        | Register::H
        | Register::L
        | Register::M,
      )],
    ) => false,
    (POP, &[OperandNode::Register(Register::B | Register::D | Register::H | Register::PSW)]) => {
      false
    }
    (PUSH, &[OperandNode::Register(Register::B | Register::D | Register::H | Register::PSW)]) => {
      false
    }

    // a16 operands
    // TODO: Change this to accept idents, literals, and expressions
    (SHLD, &[OperandNode::Literal(_)]) => false,
    (STA, &[OperandNode::Literal(_)]) => false,
    (LHLD, &[OperandNode::Literal(_)]) => false,
    (LDA, &[OperandNode::Literal(_)]) => false,
    (JNZ, &[OperandNode::Identifier(_)]) => false,
    (JNC, &[OperandNode::Identifier(_)]) => false,
    (JPO, &[OperandNode::Identifier(_)]) => false,
    (JP, &[OperandNode::Identifier(_)]) => false,
    (JMP, &[OperandNode::Identifier(_)]) => false,
    (CNZ, &[OperandNode::Identifier(_)]) => false,
    (CNC, &[OperandNode::Identifier(_)]) => false,
    (CPO, &[OperandNode::Identifier(_)]) => false,
    (CP, &[OperandNode::Identifier(_)]) => false,
    (JZ, &[OperandNode::Identifier(_)]) => false,
    (JC, &[OperandNode::Identifier(_)]) => false,
    (JPE, &[OperandNode::Identifier(_)]) => false,
    (JM, &[OperandNode::Identifier(_)]) => false,
    (CZ, &[OperandNode::Identifier(_)]) => false,
    (CC, &[OperandNode::Identifier(_)]) => false,
    (CPE, &[OperandNode::Identifier(_)]) => false,
    (CM, &[OperandNode::Identifier(_)]) => false,
    (CALL, &[OperandNode::Identifier(_)]) => false,

    // d8 operands
    (ADI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (ADI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    (SUI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (SUI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    (ANI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (ANI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    (ORI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (ORI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    (ACI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (ACI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    (SBI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (SBI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    (XRI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (XRI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    (CPI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (CPI, &[OperandNode::String(ref x)]) if x.len() == 1 => false,
    // Special instruction that only takes 0..8
    (RST, &[OperandNode::Literal(0..=7)]) => false,

    // 0 operands
    (
      NOP | HLT | RLC | RAL | DAA | STC | RRC | RAR | CMA | CMC | RNZ | RNC | RPO | RP | RZ | RC
      | RPE | RM | RET | PCHL | SPHL | XCHG,
      _,
    ) => false,

    // Anything else is an error
    _ => true,
  }
}

fn parse_number(num: &str, base: Option<u8>, token_span: Range<usize>) -> ParseResult<u16> {
  let radix = match base {
    Some(b'B') => 2,
    Some(b'O' | b'Q') => 8,
    Some(b'D') | None => 10,
    Some(b'H') => 16,
    Some(_) => {
      // TODO: This should be unreachable, since the lexer handles this, no?
      return Err(ParseError {
        start_pos: token_span.end - 1,
        kind: ParserErrorKind::InvalidNumber,
      });
    }
  };

  u16::from_str_radix(num, radix).map_err(|err| match err.kind() {
    // TODO: This should also be invalid, no?
    IntErrorKind::InvalidDigit => ParseError {
      start_pos: token_span.start,
      kind: ParserErrorKind::InvalidNumber,
    },
    IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => ParseError {
      start_pos: token_span.start,
      kind: ParserErrorKind::InvalidNumber,
    },
    // These cases wouldn't happen
    _ => unreachable!("invalid integer parsing"),
  })
}

#[cfg(test)]
mod tests {
  use types::{ParseError, ParserErrorKind};

  macro_rules! parse_and_write {
    ($src:literal) => {
      let source = include_str!(concat!("../../test_files/", $src, ".asm"));
      let program_node = crate::parse(source).unwrap();

      assert!(!program_node.children().is_empty());

      if matches!(std::fs::exists("../output/parser/"), Ok(false)) {
        std::fs::create_dir("../output/parser/").unwrap();
      }

      std::fs::write(
        concat!("../output/parser/", $src, ".txt"),
        &program_node.to_string(),
      )
      .unwrap();
    };
  }

  #[test]
  fn using_d8_string() {
    assert!(crate::parse("MVI A, 'B'").is_ok(), "using string for d8");

    assert_eq!(
      crate::parse("MVI A, 'BOO'").unwrap_err(),
      types::Error::Parser(ParseError {
        start_pos: 0,
        kind: ParserErrorKind::InvalidOperandType,
      }),
      "using multi byte string for d8"
    );

    assert!(
      crate::parse("MVI A, 'BOO").is_err(),
      "using unclosed multi byte string for d8"
    );
  }

  #[test]
  fn invalid_op_types() {
    assert_eq!(
      crate::parse("MVI A, BOO").unwrap_err(),
      types::Error::Parser(ParseError {
        start_pos: 0,
        kind: ParserErrorKind::InvalidOperandType,
      }),
      "using identifier instead of d8"
    );

    assert_eq!(
      crate::parse("MVI A, FFFFH").unwrap_err(),
      types::Error::Parser(ParseError {
        start_pos: 0,
        kind: ParserErrorKind::InvalidOperandType,
      }),
      "using d16 instead of d8"
    );
  }

  #[test]
  fn linebreak() {
    assert_eq!(
      crate::parse("MVI A, 01H MVI B, 02H").unwrap_err(),
      types::Error::Parser(ParseError {
        start_pos: 10,
        kind: ParserErrorKind::ExpectedLinebreak,
      })
    );

    assert_eq!(
      crate::parse("MVI A, 01H\nMVI B, 02H HLT").unwrap_err(),
      types::Error::Parser(ParseError {
        start_pos: 21,
        kind: ParserErrorKind::ExpectedLinebreak,
      })
    );

    // If there are no more instructions, then it's also valid
    assert!(crate::parse("MVI A, 01H").is_ok());
  }

  #[test]
  fn parser_doesnt_panic() {
    parse_and_write!("add_two_bytes");
    parse_and_write!("even_numbers_in_array");
    parse_and_write!("max_array_value");
    parse_and_write!("min_num_in_n_array");
    parse_and_write!("num_zeros_in_byte");
    parse_and_write!("occurrences_of_num");
    parse_and_write!("ones_complement");
    parse_and_write!("add_two_bytes");
    parse_and_write!("pos_or_neg");
    parse_and_write!("sum_of_array");
    parse_and_write!("twos_complement");
  }
}
