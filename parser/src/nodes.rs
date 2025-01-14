use lexer::{instruction::Instruction, Register};
use smol_str::SmolStr;

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
}

/// A node representing a label.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LabelNode {
  name: SmolStr,
}

/// A node representing an instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionNode {
  // TODO: SmallVec or just use an array?
  pub operands: Vec<OperandNode>,
  instruction: Instruction,
}

/// A node representating an expression that gets evalauted during assemble time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpressionNode {
  /// A string literal.
  String(SmolStr),
  /// An identifier.
  Identifier(SmolStr),
  /// A numeric literal.
  ///
  /// This is an i32 because unary minus is allowed.
  Number(i32),
  /// An expression wrapped in parenthesis.
  Paren(Box<ExpressionNode>),
  /// A unary expression.
  ///
  /// The unary operators are `+`, `-`, `HIGH`, and `LOW`.
  Unary {
    op: Operator,
    expr: Box<ExpressionNode>,
  },
  /// A binary expression.
  Binary {
    op: Operator,
    left: Box<ExpressionNode>,
    right: Box<ExpressionNode>,
  },
}

/// Possible operators that can be applied.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Operator {
  Addition,
  Subtraction,
  Division,
  Multiplication,
  Modulo,
  ShiftLeft,
  ShiftRight,
  Not,
  And,
  High,
  Low,
  Or,
  Xor,
  Eq,
  Ne,
  Lt,
  Le,
  Ge,
  Gt,
}

/// A node representing the operands of an instruction.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OperandNode {
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

impl ProgramNode {
  /// Creates a new [ProgramNode] from the given nodes
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
  pub fn new(name: SmolStr) -> Self {
    Self { name }
  }

  /// The name of this label, without the colon.
  pub fn label_name(&self) -> SmolStr {
    self.name.clone()
  }
}

impl InstructionNode {
  /// Creates an [`InstructionNode`] from the given instruction and operands
  pub fn from_operands(instruction: Instruction, operands: Vec<OperandNode>) -> Self {
    Self {
      instruction,
      operands,
    }
  }

  /// Creates an [`InstructionNode`] from the given instruction.
  pub fn new(instruction: Instruction) -> Self {
    const MAX_OPERANDS: usize = 2;

    Self::from_operands(instruction, Vec::with_capacity(MAX_OPERANDS))
  }

  /// The instruction of this node.
  pub const fn instruction(&self) -> Instruction {
    self.instruction
  }

  /// The operands of this node.
  pub fn operands(&self) -> &[OperandNode] {
    &self.operands
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

impl std::fmt::Display for OperandNode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      OperandNode::Identifier(ident) => write!(f, "{}", &ident),
      OperandNode::Register(reg) => write!(f, "{}", reg),
      OperandNode::Numeric(num) => write!(f, "{}", num),
      OperandNode::String(str) => write!(f, "{}", str),
      OperandNode::Expression(expr) => expr.fmt(f),
    }
  }
}

impl std::fmt::Display for LabelNode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}:", self.label_name())
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
      }
    }

    Ok(())
  }
}

impl std::fmt::Display for ExpressionNode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ExpressionNode::Number(num) => write!(f, "{}", num),
      ExpressionNode::Identifier(s) => write!(f, "{}", s),
      ExpressionNode::String(s) => write!(f, "'{}'", s),
      ExpressionNode::Unary { op, expr } => write!(f, "{}{}", op, expr),
      ExpressionNode::Binary { op, left, right } => write!(f, "{} {} {}", left, op, right),
      ExpressionNode::Paren(inner) => write!(f, "({})", inner),
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
