use crate::error::{ParseError, ParseResult};
use crate::nodes::{InstructionNode, LabelNode, Node, OperandNode, ProgramNode};
use lexer::instruction::Instruction;
use lexer::token::{Token, TokenKind};
use lexer::{Lexer, Register};
use std::num::IntErrorKind;
use std::ops::Range;

pub struct Parser<'a> {
  source: &'a str,
  tokens: Vec<Token>,
  token_index: usize,
  source_index: usize,
}

impl<'a> Parser<'a> {
  pub fn new(source: &'a str, tokens: Vec<Token>) -> Self {
    Self {
      source,
      tokens,
      token_index: 0,
      source_index: 0,
    }
  }

  pub fn from_source(source: &'a str) -> Self {
    let lexer = Lexer::from_string(source);

    Self {
      source,
      tokens: lexer.into_iter().collect::<Vec<_>>(),
      token_index: 0,
      source_index: 0,
    }
  }

  pub fn parse(&mut self) -> ParseResult<ProgramNode> {
    let mut nodes = Vec::new();

    while let Some(node) = self.parse_next() {
      nodes.push(node?);
    }

    Ok(ProgramNode::new(nodes))
  }

  pub fn parse_next(&mut self) -> Option<ParseResult<Node>> {
    // TODO: Next non-whitespace/comment fn
    let token = self.next_non_whitespace_token()?;

    Some(match token.kind() {
      // We expect a label
      TokenKind::Identifier => {
        let label_node = self.try_parse_label(&token);

        if let Some(node) = label_node {
          Ok(Node::Label(node))
        } else {
          self.source_index += token.length();
          todo!("other non label idents")
        }
      }
      TokenKind::Instruction => {
        let instruction_node = self.parse_instruction(&token);

        match instruction_node {
          Ok(node) => Ok(Node::Instruction(node)),
          Err(e) => Err(e),
        }
      }
      TokenKind::EndOfFile => return None,

      kind => {
        self.source_index += token.length();

        Err(ParseError {
          location: self.source_index..self.source_index + token.length(),
          error_message: format!("invalid token, `{}`", kind),
        })
      }
    })
  }

  /// Gets a [str] from the selected range.
  pub fn get_source_content(&self, range: Range<usize>) -> Option<&str> {
    self.source.get(range)
  }

  fn next_token(&mut self) -> Option<Token> {
    let token = self.tokens.get(self.token_index).copied();

    self.token_index += 1;

    token
  }

  fn try_parse_label(&mut self, ident_token: &Token) -> Option<LabelNode> {
    let next_token = self.next_non_whitespace_token();

    match next_token {
      Some(token) if matches!(token.kind(), TokenKind::Colon) => {
        let label_name = self
          .get_source_content(
            self.source_index..self.source_index + ident_token.length() + token.length(),
          )
          .expect("label name")
          .to_string();

        self.source_index += ident_token.length();
        // Add the prior whitespace and colon length
        self.source_index += token.length();

        Some(LabelNode::new(label_name))
      }
      _ => None,
    }
  }

  fn parse_instruction(&mut self, instruction_token: &Token) -> ParseResult<InstructionNode> {
    let instruction_str = self
      .get_source_content(self.source_index..self.source_index + instruction_token.length())
      .expect("instruction from source string");
    let instruction = Instruction::from_string(instruction_str).unwrap();

    // We saw the instruction successfully
    self.source_index += instruction_token.length();

    let num_operands = instruction.num_operands();
    let mut operands = Vec::with_capacity(num_operands);
    let mut last_token_operand = false;

    while operands.len() < num_operands {
      let token = self.next_non_whitespace_token();

      if token.is_none() {
        return Err(ParseError {
          location: self.source_index..self.source_index,
          error_message: format!(
            "expected `{}` operand(s) for the `{}` instruction",
            num_operands, instruction
          ),
        });
      }

      let token = token.unwrap();

      match token.kind() {
        //separate function for these
        TokenKind::Register => {
          let reg_str = self
            .get_source_content(self.source_index..self.source_index + token.length())
            .unwrap();
          let reg = Register::from_string(reg_str).unwrap();

          operands.push(OperandNode::Register(reg));
          last_token_operand = true;
          self.source_index += token.length();
        }
        TokenKind::Literal => {
          let mut num_str = self
            .get_source_content(self.source_index..self.source_index + token.length())
            .unwrap();
          let last_char = (*num_str.as_bytes().last().unwrap() as char).to_ascii_lowercase();
          let mut base = None;

          if matches!(last_char, 'h' | 'o' | 'b' | 'd') {
            num_str = num_str.get(..num_str.len() - 1).unwrap();
            base = Some(last_char);
          }

          let number = parse_number(num_str, base).map_err(|err| match err.kind() {
            IntErrorKind::InvalidDigit => ParseError {
              location: self.source_index..self.source_index + token.length(),
              error_message: format!("invalid number, `{}`", num_str),
            },
            IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => ParseError {
              location: self.source_index..self.source_index + token.length(),
              error_message: format!(
                "number `{}` is too large to fit in 16 bits (`{}`)",
                num_str,
                u16::MAX
              ),
            },
            _ => panic!("unhandled string int conversion"),
          })?;

          operands.push(OperandNode::Literal(number));
          last_token_operand = true;
          self.source_index += token.length();
        }
        TokenKind::Identifier => {
          let ident = self
            .get_source_content(self.source_index..self.source_index + token.length())
            .unwrap();

          operands.push(OperandNode::Identifier(ident.to_string()));
          last_token_operand = true;
          self.source_index += token.length();
        }
        TokenKind::Comma => {
          if !last_token_operand {
            return Err(ParseError {
              location: self.source_index..self.source_index + token.length(),
              error_message: format!("unexpected `{}`", token.kind()),
            });
          }

          last_token_operand = false;
          self.source_index += token.length();
        }

        _ => {
          return Err(ParseError {
            location: self.source_index..self.source_index + token.length(),
            error_message: format!("expected an operand, but found `{}`", token.kind()),
          });
        }
      }
    }

    Ok(InstructionNode::from_operands(instruction, operands))
  }

  fn next_non_whitespace_token(&mut self) -> Option<Token> {
    loop {
      let token = self.next_token()?;

      if matches!(token.kind(), TokenKind::Whitespace | TokenKind::Comment) {
        self.source_index += token.length();
      } else {
        return Some(token);
      }
    }
  }
}

fn parse_number(num: &str, base: Option<char>) -> Result<u16, std::num::ParseIntError> {
  debug_assert!(matches!(
    base,
    None | Some('b') | Some('h') | Some('o') | Some('d')
  ));

  let radix = match base {
    Some('b') => 2,
    Some('o') => 8,
    Some('d') | None => 10,
    Some('h') => 16,
    _ => panic!("invalid radix"),
  };

  u16::from_str_radix(num, radix)
}

#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! parse_file {
    ($src:literal) => {
      let source = include_str!(concat!("../../test_files/", $src, ".asm"));
      let lexer = Lexer::from_string(source);
      let tokens = lexer.into_iter().collect::<Vec<_>>();
      let mut parser = Parser::new(source, tokens);
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
