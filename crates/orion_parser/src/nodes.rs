use orion_lexer::{directive::Directive, instruction::Instruction, Register};
use smallvec::SmallVec;
use smol_str::SmolStr;
use std::ops::Range;

pub const MAX_INSTRUCTION_OPERAND_SIZE: usize = 2;
pub const MAX_DIRECTIVE_OPERAND_SIZE: usize = 8;

/// The root node for a source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgramNode {
  children: Vec<Node>,
}

/// A node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
  /// An instruction node.
  Instruction(InstructionNode),
  /// A label node.
  Label(LabelNode),
  /// An assembler directive.
  Directive(DirectiveNode),
}

/// A node representing a label.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LabelNode {
  name: SmolStr,
  span: Range<usize>,
}

/// A node representing an instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionNode {
  operands: SmallVec<[OperandNode; MAX_INSTRUCTION_OPERAND_SIZE]>,
  instruction: Instruction,
  span: Range<usize>,
}

/// A node representing an assembler directive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectiveNode {
  name: Option<SmolStr>,
  operands: SmallVec<[OperandNode; MAX_DIRECTIVE_OPERAND_SIZE]>,
  directive: Directive,
  span: Range<usize>,
}

/// A node representing the operands of an instruction.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OperandNode {
  /// The operand itself.
  pub operand: Operand,
  /// The span of this operand node.
  pub span: Range<usize>,
}

/// A type of value that can be passed as an operand.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Operand {
  /// For register operands.
  Register(Register),
  /// For numeric literals.
  Numeric(u16),
  /// For identifiers such as labels and reserved identifiers (`$`).
  Identifier(SmolStr),
  /// For operands enclosed in single quotes.
  String(SmolStr),
  /// An expression node that gets computed during assemble time.
  Expression(ExpressionNode),
}

/// A node representating an expression that gets evalauted during assemble time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionNode {
  pub expr: Expression,
  pub span: Range<usize>,
}

/// A king of expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
  /// A string literal.
  String(SmolStr),
  /// An identifier.
  Identifier(SmolStr),
  /// A numeric literal.
  Number(u16),
  /// An expression wrapped in parenthesis.
  Paren(Box<ExpressionNode>),
  /// A unary expression.
  ///
  /// The unary operators are `+`, `-`, `NOT`, `HIGH`, and `LOW`.
  Unary {
    operator: OperatorNode,
    expr: Box<ExpressionNode>,
  },
  /// A binary expression.
  Binary {
    operator: OperatorNode,
    left: Box<ExpressionNode>,
    right: Box<ExpressionNode>,
  },
}

/// An operator node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperatorNode {
  pub op: Operator,
  pub span: Range<usize>,
}

/// Possible operators that can be applied.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Operator {
  /// Unary or binary addition.
  Addition,
  /// Unary or binary subtraction.
  Subtraction,
  /// Binary integer division.
  Division,
  /// Binary multiplication.
  Multiplication,
  /// Binary modulus.
  Modulo,
  /// Binary left shift.
  ShiftLeft,
  /// Binary right shift.
  ShiftRight,
  /// Unary bit negation.
  Not,
  /// Binary bitwise AND.
  And,
  /// Unary operator that gets the upper 8 bits in a 16 bit integer.
  High,
  /// Unary operator that gets the lower 8 bits in a 16 bit integer.
  Low,
  /// Binary bitwise OR.
  Or,
  /// Binary bitwise XOR
  Xor,
  /// Binary operator equality.
  Eq,
  /// Binary operator inequality.
  Ne,
  /// Binary operator less than. This compares via bits, not values.
  Lt,
  /// Binary operator less than or equal to. This compares via bits, not values.
  Le,
  /// Binary operator greater than or equal to. This compares via bits, not values.
  Ge,
  /// Binary operator greater than or equal to. This compares via bits, not values.
  Gt,
}

impl ProgramNode {
  /// Creates a new [`ProgramNode`] from the given nodes
  pub fn new(nodes: Vec<Node>) -> Self {
    Self { children: nodes }
  }

  /// Returns the children of this node.
  pub fn children(&self) -> &[Node] {
    &self.children
  }
}

impl LabelNode {
  /// Creates a new [`LabelNode`]
  pub fn new(name: SmolStr, span: Range<usize>) -> Self {
    Self { name, span }
  }

  /// The name of this label, excluding the colon.
  pub fn label_name(&self) -> SmolStr {
    self.name.clone()
  }

  /// The span of this node in the source, including the colon.
  pub fn span(&self) -> Range<usize> {
    self.span.clone()
  }
}

impl OperandNode {
  /// Creates a new [`OperandNode`].
  pub fn new(op: Operand, span: Range<usize>) -> Self {
    Self { operand: op, span }
  }
}

impl OperatorNode {
  /// Creates a new [`OperatorNode`].
  pub fn new(op: Operator, span: Range<usize>) -> Self {
    Self { op, span }
  }
}

impl ExpressionNode {
  /// Creates a new [`ExpressionNode`].
  pub fn new(expr: Expression, span: Range<usize>) -> Self {
    Self { expr, span }
  }

  /// The [`Expression`] of this node.
  pub fn value(&self) -> &Expression {
    &self.expr
  }
}

impl InstructionNode {
  /// Creates an [`InstructionNode`] from the given instruction.
  pub fn new(instruction: Instruction, span: Range<usize>) -> Self {
    Self::from_operands(
      instruction,
      SmallVec::with_capacity(MAX_INSTRUCTION_OPERAND_SIZE),
      span,
    )
  }

  /// Creates an [`InstructionNode`] from the given instruction and operands
  pub fn from_operands(
    instruction: Instruction,
    operands: SmallVec<[OperandNode; MAX_INSTRUCTION_OPERAND_SIZE]>,
    span: Range<usize>,
  ) -> Self {
    Self {
      span,
      instruction,
      operands,
    }
  }

  /// The [`Instruction`] of this node.
  pub const fn instruction(&self) -> Instruction {
    self.instruction
  }

  /// The operands of this node.
  pub fn operands(&self) -> &[OperandNode] {
    &self.operands
  }

  /// The span of this instruction, in the source.
  pub fn span(&self) -> Range<usize> {
    self.span.clone()
  }
}

impl DirectiveNode {
  /// Creates an [`DirectiveNode`] from the given directive.
  pub fn new(name: Option<SmolStr>, directive: Directive, span: Range<usize>) -> Self {
    Self::from_operands(
      name,
      directive,
      SmallVec::with_capacity(MAX_DIRECTIVE_OPERAND_SIZE),
      span,
    )
  }

  /// Creates a [`DirectiveNode`] from the given directive and operands.
  pub fn from_operands(
    name: Option<SmolStr>,
    directive: Directive,
    operands: SmallVec<[OperandNode; MAX_DIRECTIVE_OPERAND_SIZE]>,
    span: Range<usize>,
  ) -> Self {
    Self {
      name,
      directive,
      operands,
      span,
    }
  }

  /// The identifier assigned to this directive.
  pub fn identifier(&self) -> Option<&SmolStr> {
    self.name.as_ref()
  }

  /// The [`Directive`] of this node.
  pub const fn directive(&self) -> Directive {
    self.directive
  }

  /// The operands of this node.
  pub fn operands(&self) -> &[OperandNode] {
    &self.operands
  }

  /// The span of this directive, in the source.
  pub fn span(&self) -> Range<usize> {
    self.span.clone()
  }
}

impl TryFrom<&str> for Operator {
  type Error = ();

  fn try_from(value: &str) -> Result<Self, Self::Error> {
    Ok(match value {
      x if x.eq_ignore_ascii_case("+") => Operator::Addition,
      x if x.eq_ignore_ascii_case("*") => Operator::Multiplication,
      x if x.eq_ignore_ascii_case("/") => Operator::Division,
      x if x.eq_ignore_ascii_case("-") => Operator::Subtraction,
      x if x.eq_ignore_ascii_case("mod") => Operator::Modulo,
      x if x.eq_ignore_ascii_case("shr") => Operator::ShiftRight,
      x if x.eq_ignore_ascii_case("shl") => Operator::ShiftLeft,

      x if x.eq_ignore_ascii_case("high") => Operator::Low,
      x if x.eq_ignore_ascii_case("low") => Operator::High,

      x if x.eq_ignore_ascii_case("not") => Operator::Not,
      x if x.eq_ignore_ascii_case("and") => Operator::And,
      x if x.eq_ignore_ascii_case("or") => Operator::Or,
      x if x.eq_ignore_ascii_case("xor") => Operator::Xor,

      x if x.eq_ignore_ascii_case("eq") => Operator::Eq,
      x if x.eq_ignore_ascii_case("ne") => Operator::Ne,
      x if x.eq_ignore_ascii_case("lt") => Operator::Lt,
      x if x.eq_ignore_ascii_case("le") => Operator::Le,
      x if x.eq_ignore_ascii_case("gt") => Operator::Gt,
      x if x.eq_ignore_ascii_case("ge") => Operator::Ge,

      _ => return Err(()),
    })
  }
}

impl std::fmt::Display for ProgramNode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for node in self.children() {
      match node {
        Node::Instruction(inst_node) => {
          write!(f, "{}", inst_node.instruction())?;

          let op_count = inst_node.operands().len();

          if op_count != 0 {
            for i in 0..op_count - 1 {
              write!(f, " {},", inst_node.operands.get(i).unwrap())?;
            }

            write!(f, " {}", inst_node.operands.last().unwrap())?;
          }

          writeln!(f)?;
        }
        Node::Label(label) => {
          writeln!(f, "{}", label)?;
        }
        Node::Directive(directive) => {
          writeln!(f, "{}", directive)?;
        }
      }
    }

    Ok(())
  }
}

impl std::fmt::Display for OperandNode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", self.operand)
  }
}

impl std::fmt::Display for ExpressionNode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.expr)
  }
}

impl std::fmt::Display for LabelNode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}:", self.label_name())
  }
}

impl std::fmt::Display for DirectiveNode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.directive)
  }
}

impl std::fmt::Display for OperatorNode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.op)
  }
}

impl std::fmt::Display for Operand {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Operand::Identifier(ident) => write!(f, "{}", &ident),
      Operand::Register(reg) => write!(f, "{}", reg),
      Operand::Numeric(num) => write!(f, "{}", num),
      Operand::String(str) => write!(f, "{}", str),
      Operand::Expression(expr) => expr.fmt(f),
    }
  }
}

impl std::fmt::Display for Expression {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Expression::Number(num) => write!(f, "{}", num),
      Expression::Identifier(s) => write!(f, "{}", s),
      Expression::String(s) => write!(f, "'{}'", s),
      Expression::Unary { operator: op, expr } => write!(f, "{}{}", op, expr),
      Expression::Binary {
        operator: op,
        left,
        right,
      } => write!(f, "{} {} {}", left, op, right),
      Expression::Paren(inner) => write!(f, "({})", inner),
    }
  }
}

impl std::fmt::Display for Operator {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Operator::Addition => write!(f, "+"),
      Operator::Subtraction => write!(f, "-"),
      Operator::Division => write!(f, "/"),
      Operator::Multiplication => write!(f, "*"),
      Operator::Modulo => write!(f, "MOD"),
      Operator::ShiftLeft => write!(f, "SHL"),
      Operator::ShiftRight => write!(f, "SHR"),
      Operator::Not => write!(f, "NOT"),
      Operator::And => write!(f, "AND"),
      Operator::High => write!(f, "HIGH"),
      Operator::Low => write!(f, "LOW"),
      Operator::Or => write!(f, "OR"),
      Operator::Xor => write!(f, "XOR"),
      Operator::Eq => write!(f, "EQ"),
      Operator::Ne => write!(f, "NE"),
      Operator::Lt => write!(f, "LT"),
      Operator::Le => write!(f, "LE"),
      Operator::Ge => write!(f, "GE"),
      Operator::Gt => write!(f, "GT"),
    }
  }
}
