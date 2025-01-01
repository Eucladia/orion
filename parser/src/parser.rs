use crate::error::{ParseError, ParseResult};
use crate::nodes::{InstructionNode, LabelNode, Node, OperandNode, ProgramNode};
use crate::unwrap;

use lexer::instruction::Instruction;
use lexer::token::{Token, TokenKind};
use lexer::LexerResult;
use lexer::{Lexer, Register};
use smol_str::SmolStr;
use std::num::IntErrorKind;
use std::ops::Range;

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

  pub fn from_source(source: &'a str) -> LexerResult<Self> {
    let lexer = Lexer::from_string(source);

    Ok(Self {
      source,
      tokens: lexer.into_iter().collect::<LexerResult<Vec<_>>>()?,
      token_index: 0,
    })
  }

  /// Gets a [str] from the selected range.
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

    Some(match token.kind() {
      // We expect a label
      TokenKind::Identifier => {
        let label_node = self.try_parse_label(&token);

        if let Some(node) = label_node {
          Ok(Node::Label(node))
        } else {
          // TODO: Parse directives here
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

      kind => Err(ParseError {
        location: token.span(),
        error_message: format!("invalid token, `{}`", kind),
      }),
    })
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
    // SAFETY: We have an immutable str and the lexer produced this `Instruction` token, so this str is still valid
    let instruction_str = unwrap!(self.get_source_content(instruction_token.span()));
    let instruction = unwrap!(Instruction::from_string(instruction_str));

    let num_operands = instruction.num_operands();
    let mut operands = Vec::with_capacity(num_operands);
    let mut last_token_operand = false;

    while operands.len() < num_operands {
      let token = self.next_non_whitespace_token();

      if token.is_none() {
        return Err(ParseError {
          location: self.source.len()..self.source.len(),
          error_message: format!(
            "expected `{}` operand(s) for the `{}` instruction",
            num_operands, instruction
          ),
        });
      }

      // SAFETY: We check if it's `None` above
      let token = unwrap!(token);

      match token.kind() {
        // TODO: separate function for these
        TokenKind::Register => {
          // SAFETY: We have a valid `Register` token produced from the lexer and an immutable str
          let reg_str = unwrap!(self.get_source_content(token.span()));
          let reg = unwrap!(Register::from_string(reg_str));

          operands.push(OperandNode::Register(reg));
          last_token_operand = true;
        }
        TokenKind::Literal => {
          // SAFETY: We have a valid `Literal` token produced from the lexer and an immutable str
          let mut num_str = unwrap!(self.get_source_content(token.span()));
          // SAFETY: We're guaranteed at least one byte for `Literal`s.
          let last_byte = unwrap!(num_str.as_bytes().last()).to_ascii_lowercase();
          let mut base = None;

          if matches!(last_byte, b'h' | b'o' | b'b' | b'd') {
            // SAFETY: We have at least one byte in this token
            num_str = unwrap!(num_str.get(..num_str.len() - 1));
            base = Some(last_byte);
          }

          let number = parse_number(num_str, base, token.span())?;

          operands.push(OperandNode::Literal(number));
          last_token_operand = true;
        }
        TokenKind::Identifier => {
          // SAFETY: We have a valid `Identifier` token produced by the lexer and an immutable str
          let ident = unwrap!(self.get_source_content(token.span()));

          operands.push(OperandNode::Identifier(SmolStr::new(ident.to_string())));
          last_token_operand = true;
        }
        TokenKind::Comma => {
          if !last_token_operand {
            return Err(ParseError {
              location: token.span(),
              error_message: format!("unexpected `{}`", token.kind()),
            });
          }

          last_token_operand = false;
        }

        _ => {
          return Err(ParseError {
            location: token.span(),
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

      if !matches!(token.kind(), TokenKind::Whitespace | TokenKind::Comment) {
        return Some(token.clone());
      }
    }
  }
}

fn parse_number(num: &str, base: Option<u8>, token_span: Range<usize>) -> ParseResult<u16> {
  let radix = match base {
    Some(b'b') => 2,
    Some(b'o') => 8,
    Some(b'd') | None => 10,
    Some(b'h') => 16,
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
      let tokens = lexer.into_iter().collect::<LexerResult<Vec<_>>>();
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
