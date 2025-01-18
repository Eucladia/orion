use crate::nodes::{
  Expression, ExpressionNode, InstructionNode, LabelNode, Node, Operand, OperandNode, Operator,
  ProgramNode,
};
use crate::unwrap;

use lexer::instruction::Instruction;
use lexer::token::{Token, TokenKind};
use lexer::Register;
use smallvec::SmallVec;
use types::{LexResult, ParseError, ParseErrorKind, ParseResult};

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
  /// Creates a new [`Parser`] from the set of tokens.
  pub fn new(source: &'a str, mut tokens: Vec<Token>) -> Self {
    // Get rid of the EOF token
    if matches!(tokens.last().map(Token::kind), Some(TokenKind::EndOfFile)) {
      tokens.pop();
    }

    Self {
      source,
      tokens,
      token_index: 0,
    }
  }

  /// Creates a new [`Parser`] from a source string.
  pub fn from_source(source: &'a str) -> LexResult<Self> {
    let mut tokens = lexer::lex(source)?;

    // Get rid of the EOF token
    tokens.pop();

    Ok(Self {
      source,
      tokens,
      token_index: 0,
    })
  }

  /// Gets a [`str`] from the selected range.
  pub fn get_source_content(&self, range: Range<usize>) -> Option<&str> {
    self.source.get(range)
  }

  /// Parses the source into an AST.
  pub fn parse(&mut self) -> ParseResult<ProgramNode> {
    let mut nodes = Vec::new();

    while let Some(node) = self.parse_next() {
      nodes.push(node?);
    }

    Ok(ProgramNode::new(nodes))
  }

  /// Parses the next node.
  pub fn parse_next(&mut self) -> Option<ParseResult<Node>> {
    let token = self.next_non_whitespace_token()?;

    match token.kind() {
      TokenKind::Identifier => {
        let ident = unwrap!(self.get_source_content(token.span()));

        if ident.starts_with("$") && ident.len() > 1 {
          return Some(Err(ParseError::new(
            token.span().start,
            ParseErrorKind::ReservedIdentifier,
          )));
        }

        let label_node = self.try_parse_label(&token);

        if let Some(node) = label_node {
          if node.label_name().len() > MAX_LABEL_NAME {
            Some(Err(ParseError::new(
              token.span().start,
              ParseErrorKind::InvalidLabelLength,
            )))
          } else {
            Some(Ok(Node::Label(node)))
          }
        } else {
          // TODO: Parse directives here
          todo!("other non label idents")
        }
      }
      TokenKind::Instruction => {
        let instruction_node = self.parse_instruction(token);

        Some(match instruction_node {
          Ok(node) => Ok(Node::Instruction(node)),
          Err(e) => Err(e),
        })
      }

      _ => Some(Err(ParseError::new(
        token.span().start,
        ParseErrorKind::UnexpectedToken,
      ))),
    }
  }

  fn try_parse_label(&mut self, ident_token: &Token) -> Option<LabelNode> {
    let next_token = self.next_non_whitespace_token();

    match next_token {
      Some(colon_token) if matches!(colon_token.kind(), TokenKind::Colon) => {
        // SAFETY: We have a valid identifier token and we just checked for a colon, given
        // the immutable source str
        let label_name = unwrap!(self.get_source_content(ident_token.span())).to_string();

        Some(LabelNode::new(
          SmolStr::new(&label_name),
          ident_token.span(),
        ))
      }
      _ => None,
    }
  }

  fn parse_instruction(&mut self, instruction_token: Token) -> ParseResult<InstructionNode> {
    // SAFETY: We have an immutable str and the lexer produced this `Instruction` token,
    // so this str is still valid
    let instruction_str = unwrap!(self.get_source_content(instruction_token.span()));
    let instruction = unwrap!(Instruction::from_string(instruction_str));

    let num_operands = instruction.num_operands();
    let mut operands = SmallVec::with_capacity(num_operands);
    let mut last_token_operand = false;

    while operands.len() < num_operands {
      match self.next_token() {
        Some(token)
          if matches!(token.kind(), TokenKind::Numeric)
            // The only valid unary operator is minus
            || (matches!(token.kind(), TokenKind::Operator)
            && matches!(self.source.get(token.span()), Some("-"))) =>
        {
          if matches!(
            self
              .peek_token_from_n(self.token_index + 1)
              .as_ref()
              .map(Token::kind),
            Some(TokenKind::Operator)
          ) {
            self.token_index -= 1;

            let expr = self.parse_expr()?;
            let span = token.span().start..self.previous_token().unwrap().span().end;

            operands.push(OperandNode::new(Operand::Expression(expr), span))
          } else if matches!(token.kind(), TokenKind::Operator) {
            let Some(number_token) = self.next_token() else {
              return Err(ParseError::new(
                token.span().end,
                ParseErrorKind::ExpectedOperand,
              ));
            };
            let num = parse_number(self.source, &number_token)?;

            operands.push(OperandNode::new(
              Operand::Numeric(num),
              token.span().start..number_token.span().end,
            ));
          } else {
            let num = parse_number(self.source, &token)?;

            operands.push(OperandNode::new(Operand::Numeric(num), token.span()));
          }

          last_token_operand = true;
        }
        Some(token) if matches!(token.kind(), TokenKind::Identifier) => {
          if matches!(
            self.peek_token().as_ref().map(Token::kind),
            Some(TokenKind::Operator)
          ) {
            self.token_index -= 1;

            let expr = self.parse_expr()?;
            let span = token.span().start..self.previous_token().unwrap().span().end;

            operands.push(OperandNode::new(Operand::Expression(expr), span))
          } else {
            // SAFETY: We have a valid `Identifier` token produced by the lexer and an immutable str
            operands.push(OperandNode::new(
              Operand::Identifier(SmolStr::new(unwrap!(self.source.get(token.span())))),
              token.span(),
            ))
          }

          last_token_operand = true;
        }
        Some(token) if matches!(token.kind(), TokenKind::String) => {
          if matches!(
            self.peek_token().as_ref().map(Token::kind),
            Some(TokenKind::Operator)
          ) {
            self.token_index -= 1;

            let expr = self.parse_expr()?;
            let span = token.span().start..self.previous_token().unwrap().span().end;

            operands.push(OperandNode::new(Operand::Expression(expr), span))
          } else {
            operands.push(OperandNode::new(
              Operand::String(parse_string(self.source, &token)?),
              token.span(),
            ))
          }

          last_token_operand = true;
        }
        Some(token) if matches!(token.kind(), TokenKind::Register) => {
          // SAFETY: We have a valid `Register` token produced from the lexer and an immutable str
          let reg_str = unwrap!(self.get_source_content(token.span()));
          let reg = unwrap!(Register::from_string(reg_str));

          operands.push(OperandNode::new(Operand::Register(reg), token.span()));
          last_token_operand = true;
        }
        Some(token) if matches!(token.kind(), TokenKind::Comma) => {
          if !last_token_operand {
            return Err(ParseError::new(
              token.span().start,
              ParseErrorKind::UnexpectedToken,
            ));
          }

          last_token_operand = false;
        }
        Some(token) if matches!(token.kind(), TokenKind::LeftParenthesis) => {
          self.token_index -= 1;

          let expr = self.parse_expr()?;
          let span = token.span().start..self.previous_token().unwrap().span().end;

          operands.push(OperandNode::new(Operand::Expression(expr), span));
          last_token_operand = true;
        }
        Some(token) => {
          return Err(ParseError::new(
            token.span().start,
            ParseErrorKind::InvalidOperand,
          ));
        }
        None => {
          return Err(ParseError::new(
            self.source.len(),
            ParseErrorKind::ExpectedOperand,
          ));
        }
      }
    }

    // We have a valid statement if it's not the last statement or if the statement is
    // terminated with a linebreak.
    //
    // `peek_token` can also return `None`, if it saw a linebreak.
    let got_linebreak = self.peek_token().is_none() && self.token_index < self.tokens.len();
    let prev_token = self
      .previous_token()
      .expect("previous token shouldn't be empty");

    if self.peek_non_whitespace_token().is_some() && !got_linebreak {
      return Err(ParseError::new(
        // Point to the end of the last token
        prev_token.span().end,
        ParseErrorKind::ExpectedLinebreak,
      ));
    }

    Ok(InstructionNode::from_operands(
      instruction,
      operands,
      instruction_token.span().start..prev_token.span().end,
    ))
  }

  /// Peeks the previous non-whitespace token, without modifying the internal counter
  fn previous_token(&self) -> Option<Token> {
    let mut index = self.token_index.min(self.tokens.len());

    loop {
      if index == 0 {
        return None;
      }

      index -= 1;

      let token = self.tokens.get(index)?;

      if !matches!(
        token.kind(),
        TokenKind::Linebreak | TokenKind::Whitespace | TokenKind::Comment
      ) {
        return Some(token.clone());
      }
    }
  }

  /// Peeks the next non-whitespace token, starting from position  `n`, on the current line.
  fn peek_token_from_n(&self, mut token_index: usize) -> Option<Token> {
    loop {
      let token = self.tokens.get(token_index)?;

      if matches!(token.kind(), TokenKind::Linebreak) {
        return None;
      }

      token_index += 1;

      if !matches!(token.kind(), TokenKind::Whitespace | TokenKind::Comment) {
        return Some(token.clone());
      }
    }
  }

  /// Peeks the next non-whitespace token, on the current line.
  fn peek_token(&self) -> Option<Token> {
    self.peek_token_from_n(self.token_index)
  }

  /// Peeks the next non-whitespace token.
  fn peek_non_whitespace_token(&self) -> Option<Token> {
    let mut index = self.token_index;

    loop {
      let token = self.tokens.get(index)?;

      index += 1;

      if !matches!(
        token.kind(),
        TokenKind::Linebreak | TokenKind::Whitespace | TokenKind::Comment
      ) {
        return Some(token.clone());
      }
    }
  }

  /// Gets the next non-whitespace token, on the current line.
  fn next_token(&mut self) -> Option<Token> {
    loop {
      let token = self.tokens.get(self.token_index)?;

      if matches!(token.kind(), TokenKind::Linebreak) {
        return None;
      }

      self.token_index += 1;

      if !matches!(token.kind(), TokenKind::Whitespace | TokenKind::Comment) {
        return Some(token.clone());
      }
    }
  }

  /// Gets the next non-whitespace token.
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

  // Start parsing starting from OR or XOR
  fn parse_expr(&mut self) -> ParseResult<ExpressionNode> {
    let Some(start_span) = self.peek_token().as_ref().map(|x| x.span().start) else {
      return Err(ParseError::new(
        self.previous_token().unwrap().span().end,
        ParseErrorKind::ExpectedOperand,
      ));
    };
    let mut lhs = self.parse_logical_and()?;

    while let Some(tok) = self.next_token() {
      let op = Operator::try_from(self.source.get(tok.span()).unwrap()).ok();

      if !matches!(op, Some(Operator::Or | Operator::Xor)) {
        // Not the proper token, so go back
        self.token_index -= 1;
        break;
      }

      let rhs = self.parse_logical_and()?;

      lhs = ExpressionNode::new(
        Expression::Binary {
          left: Box::new(lhs),
          op: op.unwrap(),
          right: Box::new(rhs),
        },
        start_span..self.previous_token().unwrap().span().end,
      );
    }

    Ok(lhs)
  }

  fn parse_logical_and(&mut self) -> ParseResult<ExpressionNode> {
    let Some(start_span) = self.peek_token().as_ref().map(|x| x.span().start) else {
      return Err(ParseError::new(
        self.previous_token().unwrap().span().end,
        ParseErrorKind::ExpectedOperand,
      ));
    };
    let mut lhs = self.parse_relational()?;

    while let Some(tok) = self.next_token() {
      let op = Operator::try_from(self.source.get(tok.span()).unwrap()).ok();

      if !matches!(op, Some(Operator::And)) {
        self.token_index -= 1;
        break;
      }

      let rhs = self.parse_relational()?;

      lhs = ExpressionNode::new(
        Expression::Binary {
          left: Box::new(lhs),
          op: op.unwrap(),
          right: Box::new(rhs),
        },
        start_span..self.previous_token().unwrap().span().end,
      );
    }

    Ok(lhs)
  }

  fn parse_relational(&mut self) -> ParseResult<ExpressionNode> {
    let Some(start_span) = self.peek_token().as_ref().map(|x| x.span().start) else {
      return Err(ParseError::new(
        self.previous_token().unwrap().span().end,
        ParseErrorKind::ExpectedOperand,
      ));
    };
    let mut lhs = self.parse_addition()?;

    while let Some(tok) = self.next_token() {
      let op = Operator::try_from(self.source.get(tok.span()).unwrap()).ok();

      if !matches!(
        op,
        Some(
          Operator::Eq | Operator::Ne | Operator::Lt | Operator::Le | Operator::Gt | Operator::Ge
        )
      ) {
        self.token_index -= 1;
        break;
      }

      let rhs = self.parse_addition()?;

      lhs = ExpressionNode::new(
        Expression::Binary {
          left: Box::new(lhs),
          op: op.unwrap(),
          right: Box::new(rhs),
        },
        start_span..self.previous_token().unwrap().span().end,
      );
    }

    Ok(lhs)
  }

  fn parse_addition(&mut self) -> ParseResult<ExpressionNode> {
    let Some(start_span) = self.peek_token().as_ref().map(|x| x.span().start) else {
      return Err(ParseError::new(
        self.previous_token().unwrap().span().end,
        ParseErrorKind::ExpectedOperand,
      ));
    };
    let mut lhs = self.parse_multiplication()?;

    while let Some(tok) = self.next_token() {
      let op = Operator::try_from(self.source.get(tok.span()).unwrap()).ok();

      if !matches!(op, Some(Operator::Addition)) {
        self.token_index -= 1;
        break;
      }

      let rhs = self.parse_multiplication()?;

      lhs = ExpressionNode::new(
        Expression::Binary {
          left: Box::new(lhs),
          op: op.unwrap(),
          right: Box::new(rhs),
        },
        start_span..self.previous_token().unwrap().span().end,
      );
    }

    Ok(lhs)
  }

  fn parse_multiplication(&mut self) -> ParseResult<ExpressionNode> {
    let Some(start_span) = self.peek_token().as_ref().map(|x| x.span().start) else {
      return Err(ParseError::new(
        self.previous_token().unwrap().span().end,
        ParseErrorKind::ExpectedOperand,
      ));
    };
    let mut lhs = self.parse_unary()?;

    while let Some(tok) = self.next_token() {
      let op = Operator::try_from(self.source.get(tok.span()).unwrap()).ok();

      if !matches!(op, Some(Operator::Multiplication)) {
        self.token_index -= 1;
        break;
      }

      let rhs = self.parse_unary()?;

      lhs = ExpressionNode::new(
        Expression::Binary {
          left: Box::new(lhs),
          op: op.unwrap(),
          right: Box::new(rhs),
        },
        start_span..self.previous_token().unwrap().span().end,
      );
    }

    Ok(lhs)
  }

  fn parse_unary(&mut self) -> ParseResult<ExpressionNode> {
    let tok = self.next_token();

    if tok.is_none() {
      return Err(ParseError::new(
        self.source.len(),
        ParseErrorKind::ExpectedOperand,
      ));
    }

    let tok = tok.unwrap();
    let op = Operator::try_from(self.source.get(tok.span()).unwrap()).ok();

    if matches!(
      op,
      Some(
        Operator::Addition | Operator::Subtraction | Operator::High | Operator::Low | Operator::Not
      )
    ) {
      let expr = self.parse_unary()?;

      Ok(ExpressionNode::new(
        Expression::Unary {
          op: op.unwrap(),
          expr: Box::new(expr),
        },
        tok.span().start..self.previous_token().unwrap().span().end,
      ))
    } else {
      self.token_index -= 1;
      self.parse_factor()
    }
  }

  fn parse_factor(&mut self) -> ParseResult<ExpressionNode> {
    match self.peek_token() {
      Some(tok) if matches!(tok.kind(), TokenKind::Identifier) => {
        self.next_token();

        Ok(ExpressionNode::new(
          Expression::Identifier(SmolStr::new(self.source.get(tok.span()).unwrap())),
          tok.span(),
        ))
      }
      Some(tok) if matches!(tok.kind(), TokenKind::String) => {
        self.next_token();

        Ok(ExpressionNode::new(
          Expression::String(SmolStr::new(parse_string(self.source, &tok)?)),
          tok.span(),
        ))
      }
      Some(tok) if matches!(tok.kind(), TokenKind::Numeric) => {
        self.next_token();

        Ok(ExpressionNode::new(
          Expression::Number(parse_expression_number(self.source, &tok)?),
          tok.span(),
        ))
      }
      Some(tok) if matches!(tok.kind(), TokenKind::LeftParenthesis) => {
        self.next_token();

        let expr = self.parse_expr()?;

        match self.next_token() {
          Some(t) if matches!(t.kind(), TokenKind::RightParenthesis) => Ok(ExpressionNode::new(
            Expression::Paren(Box::new(expr)),
            tok.span().start..t.span().end,
          )),
          Some(t) => Err(ParseError::new(
            t.span().start,
            ParseErrorKind::InvalidOperand,
          )),

          None => Err(ParseError::new(
            tok.span().start,
            ParseErrorKind::ExpectedOperand,
          )),
        }
      }
      Some(tok) => Err(ParseError::new(
        tok.span().start,
        ParseErrorKind::InvalidOperand,
      )),
      None => Err(ParseError::new(
        self.source.len(),
        ParseErrorKind::ExpectedOperand,
      )),
    }
  }
}

/// Parses the text delimited in single quotes from a [`Token`], failing if the string is
/// longer than 128 characters.
fn parse_string(source: &str, token: &Token) -> ParseResult<SmolStr> {
  let span = token.span();

  // Don't include the starting and opening quotes
  if span.end - span.start - 2 > 128 {
    return Err(ParseError::new(
      span.start,
      ParseErrorKind::InvalidStringLength,
    ));
  }

  let mut str = SmolStrBuilder::new();
  let contents = source.as_bytes().get(span.start + 1..span.end - 1).unwrap();
  let mut escaped_quote = false;

  for &byte in contents.iter() {
    if byte == b'\'' {
      // We should insert this `'` because it's escaped
      if escaped_quote {
        str.push(byte as char);
      }

      escaped_quote = !escaped_quote;
    } else {
      str.push(byte as char);
    }
  }

  Ok(str.finish())
}

/// Parses a number for an expression, where negative numbers can be allowed.
fn parse_expression_number(src: &str, token: &Token) -> ParseResult<u16> {
  // SAFETY: We have a valid `Literal` token produced from the lexer and an immutable str
  let mut num_str = unwrap!(src.get(token.span()));
  // SAFETY: We're guaranteed at least one byte for `Literal`s.
  let last_byte = unwrap!(num_str.as_bytes().last()).to_ascii_lowercase();
  let mut base = None;

  if matches!(last_byte, b'h' | b'o' | b'q' | b'b' | b'd') {
    // SAFETY: We have at least one byte in this token
    num_str = unwrap!(num_str.get(..num_str.len() - 1));
    base = Some(last_byte);
  }

  let radix = match base {
    Some(b'b') => 2,
    Some(b'o' | b'q') => 8,
    Some(b'd') | None => 10,
    Some(b'h') => 16,
    // We're guaranteed that it ends in one of the above bases.
    Some(_) => unreachable!("invalid numeric suffix"),
  };

  match i32::from_str_radix(num_str, radix) {
    Ok(x) if (-0xFFFF..=0xFFFF).contains(&x) => Ok(x as u16),
    _ => Err(ParseError::new(
      token.span().start,
      ParseErrorKind::InvalidNumber,
    )),
  }
}

/// Parses a literal number.
fn parse_number(src: &str, token: &Token) -> ParseResult<u16> {
  // SAFETY: We have a valid `Literal` token produced from the lexer and an immutable str
  let mut num_str = unwrap!(src.get(token.span()));
  // SAFETY: We're guaranteed at least one byte for `Literal`s.
  let last_byte = unwrap!(num_str.as_bytes().last()).to_ascii_lowercase();
  let mut base = None;

  if matches!(last_byte, b'h' | b'o' | b'q' | b'b' | b'd') {
    // SAFETY: We have at least one byte in this token
    num_str = unwrap!(num_str.get(..num_str.len() - 1));
    base = Some(last_byte);
  }

  let radix = match base {
    Some(b'b') => 2,
    Some(b'o' | b'q') => 8,
    Some(b'd') | None => 10,
    Some(b'h') => 16,
    // We're guaranteed that it ends in one of the above bases.
    Some(_) => unreachable!("invalid numeric suffix"),
  };

  u16::from_str_radix(num_str, radix).map_err(|err| match err.kind() {
    IntErrorKind::InvalidDigit | IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => {
      ParseError::new(token.span().start, ParseErrorKind::InvalidNumber)
    }
    // Any other cases should be unreachable, we really only care about fitting
    // the number into a u16
    _ => unreachable!("invalid integer parsing"),
  })
}

#[cfg(test)]
mod tests {
  use types::{ParseError, ParseErrorKind};

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
  fn numeric_literals() {
    assert!(crate::parse("MVI A, 0FHB").is_err(), "extra suffix");
    assert!(crate::parse("MVI A, 0FH").is_ok(), "valid hex");
    assert!(crate::parse("MVI A, 0").is_ok(), "hex");
    assert!(crate::parse("MVI A, 0H").is_ok(), "0 hex");
    assert!(
      crate::parse("MVI A, +0").is_err(),
      "unary + should be invalid"
    );
    assert!(
      crate::parse("MVI A, 0qqBoH").is_err(),
      "invalid hex with other suffix"
    );
  }

  #[test]
  fn invalid_length_strings() {
    assert!(crate::parse(&format!("LXI H, '{}'", "A".repeat(128))).is_ok());

    assert_eq!(
      crate::parse(&format!("LXI H, '{}'", "A".repeat(129))),
      Err(types::Error::Parser(ParseError::new(
        7,
        ParseErrorKind::InvalidStringLength
      )))
    );
  }

  #[test]
  fn not_enough_operands() {
    assert_eq!(
      crate::parse("MVI").unwrap_err(),
      types::Error::Parser(ParseError::new(3, ParseErrorKind::ExpectedOperand))
    );
  }

  #[test]
  fn expr_as_operand() {
    assert!(
      crate::parse("LXI H, ($ + ($ + 6) * 2 + 'A')").is_ok(),
      "multi parens operand"
    );
    assert!(
      crate::parse("LXI H, $ + ($ + 6) * 2 + 'A'").is_ok(),
      "single parens operand"
    );
    assert!(
      crate::parse("LXI H, $ + $ + 6 * 2 + 'A'").is_ok(),
      "expression"
    );
  }

  #[test]
  fn unclosed_string_operand() {
    assert!(
      crate::parse("MVI A, 'BOO").is_err(),
      "using unclosed multi byte string for d8"
    );
  }

  #[test]
  fn valid_number_suffix() {
    assert!(
      crate::parse("MVI A, 1h").is_ok(),
      "expected lowercase suffix to be valid"
    );

    assert!(
      crate::parse("MVI A, 1H").is_ok(),
      "expected uppercase suffix to be valid"
    );
  }

  #[test]
  fn reserved_words() {
    assert!(crate::parse("NOP\nNOP\nJMP $").is_ok());
  }

  #[test]
  fn linebreak() {
    assert_eq!(
      crate::parse("MVI A, 01H MVI B, 02H").unwrap_err(),
      types::Error::Parser(ParseError::new(10, ParseErrorKind::ExpectedLinebreak,)),
      "expected linebreak between MVIs"
    );

    assert_eq!(
      crate::parse("MVI A, 01H\nMVI B, 02H HLT").unwrap_err(),
      types::Error::Parser(ParseError::new(21, ParseErrorKind::ExpectedLinebreak,)),
      "expected linebreak before HLT"
    );

    // If there are no more instructions, then it's also valid
    assert!(
      crate::parse("MVI A, 01H").is_ok(),
      "single statement should be valid without linebreaks"
    );
    assert!(
      crate::parse("MVI A, 01H\nHLT").is_ok(),
      "multiple statements should still be valid"
    );
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
