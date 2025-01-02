use crate::nodes::{InstructionNode, LabelNode, Node, OperandNode, ProgramNode};
use crate::unwrap;

use lexer::instruction::Instruction;
use lexer::token::{Token, TokenKind};
use lexer::{Lexer, Register};
use types::{LexResult, ParseError, ParseResult};

use smol_str::SmolStr;

use std::collections::HashSet;
use std::num::IntErrorKind;
use std::ops::Range;

/// The maximum length of a label name.
pub const MAX_LABEL_NAME: usize = 6;

pub struct Parser<'a> {
  source: &'a str,
  tokens: Vec<Token>,
  token_index: usize,
  tracked_labels: HashSet<SmolStr>,
}

impl<'a> Parser<'a> {
  pub fn new(source: &'a str, tokens: Vec<Token>) -> Self {
    Self {
      source,
      tokens,
      token_index: 0,
      tracked_labels: HashSet::new(),
    }
  }

  pub fn from_source(source: &'a str) -> LexResult<Self> {
    let lexer = Lexer::from_string(source);

    Ok(Self {
      source,
      tokens: lexer.into_iter().collect::<LexResult<Vec<_>>>()?,
      token_index: 0,
      tracked_labels: HashSet::new(),
    })
  }

  /// Gets a [`str`] from the selected range.
  pub fn get_source_content(&self, range: Range<usize>) -> Option<&str> {
    self.source.get(range)
  }

  fn next_token(&mut self) -> Option<&Token> {
    let token = self.tokens.get(self.token_index);

    self.token_index += 1;

    token
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
            location: token.span(),
            error_message: format!("`$` is a reserved symbol and cannot be an identifier"),
          }));
        }

        let label_node = self.try_parse_label(&token);

        if let Some(node) = label_node {
          if node.label_name().len() > MAX_LABEL_NAME {
            Some(Err(ParseError {
              location: token.span(),
              error_message: format!(
                "label names cannot be greater than {MAX_LABEL_NAME} characters"
              ),
            }))
          } else if self.tracked_labels.contains(&node.label_name()) {
            Some(Err(ParseError {
              location: token.span(),
              error_message: format!("label `{}` was already defined.", node.label_name()),
            }))
          } else {
            self.tracked_labels.insert(node.label_name());

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

      kind => Some(Err(ParseError {
        location: token.span(),
        error_message: format!("invalid token, `{}`", kind),
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

    while operands.len() < num_operands {
      match self.next_non_whitespace_token() {
        Some(token) if matches!(token.kind(), TokenKind::Register) => {
          // SAFETY: We have a valid `Register` token produced from the lexer and an immutable str
          let reg_str = unwrap!(self.get_source_content(token.span()));
          let reg = unwrap!(Register::from_string(reg_str));

          operands.push(OperandNode::Register(reg));
          last_token_operand = true;
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
        }
        Some(token) if matches!(token.kind(), TokenKind::Identifier) => {
          // SAFETY: We have a valid `Identifier` token produced by the lexer and an immutable str
          let ident = unwrap!(self.get_source_content(token.span()));

          operands.push(OperandNode::Identifier(SmolStr::new(ident)));
          last_token_operand = true;
        }
        Some(token) if matches!(token.kind(), TokenKind::Comma) => {
          if !last_token_operand {
            return Err(ParseError {
              location: token.span(),
              error_message: format!("unexpected `{}`", token.kind()),
            });
          }

          last_token_operand = false;
        }
        Some(token) => {
          return Err(ParseError {
            location: token.span(),
            error_message: format!("expected an operand, but found `{}`", token.kind()),
          });
        }
        None => {
          return Err(ParseError {
            location: self.source.len()..self.source.len(),
            error_message: format!(
              "expected `{}` operand(s) for the `{}` instruction",
              num_operands, instruction
            ),
          });
        }
      }
    }

    if instruction_type_error(&instruction, &operands) {
      Err(ParseError {
        location: instruction_token.span(),
        error_message: format!("invalid types passed to this instruction"),
      })
    } else {
      Ok(InstructionNode::from_operands(instruction, operands))
    }
  }

  fn next_non_whitespace_token(&mut self) -> Option<Token> {
    loop {
      let token = self.next_token()?;

      if !matches!(token.kind(), TokenKind::Whitespace | TokenKind::Comment) {
        return Some(token.clone());
      }
    }
  }
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
    (SUI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (ANI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (ORI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (ACI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (SBI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (XRI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (CPI, &[OperandNode::Literal(x)]) if x <= u8::MAX as u16 => false,
    (RST, &[OperandNode::Literal(x)]) if matches!(x, 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7) => false,

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
    Some(x) => {
      return Err(ParseError {
        location: token_span.end - 1..token_span.end,
        error_message: format!("invalid radix `{}`", x),
      });
    }
  };

  u16::from_str_radix(num, radix).map_err(|err| match err.kind() {
    IntErrorKind::InvalidDigit => ParseError {
      location: token_span,
      error_message: format!("invalid number, `{}`", num),
    },
    IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => ParseError {
      location: token_span,
      error_message: format!(
        "number `{}` is too large to fit in 16 bits (`{}`)",
        num,
        u16::MAX
      ),
    },
    // These cases wouldn't happen
    _ => ParseError {
      location: token_span,
      error_message: format!("unhandled int conversion, `{}`", num),
    },
  })
}

#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! parse_file {
    ($src:literal) => {
      let source = include_str!(concat!("../../test_files/", $src, ".asm"));
      let lexer = Lexer::from_string(source);
      let tokens = lexer.into_iter().collect::<LexResult<Vec<_>>>();
      let mut parser = Parser::new(source, tokens.unwrap());
      let program_node = parser.parse().unwrap();

      assert!(!program_node.children().is_empty());

      if matches!(std::fs::exists("../test_files/parser_output/"), Ok(false)) {
        std::fs::create_dir("../test_files/parser_output/").unwrap();
      }

      std::fs::write(
        concat!("../test_files/parser_output/", $src, ".txt"),
        &program_node.to_string(),
      )
      .unwrap();
    };
  }

  #[test]
  fn parser_doesnt_panic() {
    parse_file!("add_two_bytes");
    parse_file!("even_numbers_in_array");
    parse_file!("max_array_value");
    parse_file!("min_num_in_n_array");
    parse_file!("num_zeros_in_byte");
    parse_file!("occurrences_of_num");
    parse_file!("ones_complement");
    parse_file!("add_two_bytes");
    parse_file!("pos_or_neg");
    parse_file!("sum_of_array");
    parse_file!("twos_complement");
  }
}
