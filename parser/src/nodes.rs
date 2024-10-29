use lexer::{instruction::Instruction, Register};
use smol_str::SmolStr;

/// The root node for a source file
#[derive(Debug, Clone)]
pub struct ProgramNode {
  children: Vec<Node>,
}

/// A node
#[derive(Debug, Clone)]
pub enum Node {
  Instruction(InstructionNode),
  Label(LabelNode),
}

/// A node representing a label
#[derive(Debug, Clone)]
pub struct LabelNode {
  name: SmolStr,
}

/// A node representing an instruction
#[derive(Debug, Clone)]
pub struct InstructionNode {
  // TODO: SmallVec or just use an array?
  pub operands: Vec<OperandNode>,
  instruction: Instruction,
}

/// A node representing the operands of an instruction
#[derive(Debug, Clone)]
pub enum OperandNode {
  /// For instructions that have an operand that is a register
  Register(Register),
  /// For instructions that contain numeric literals – eg memory addresses or numbers
  Literal(u16),
  /// For instructions that have labels
  Identifier(String),
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
  pub fn new(name: SmolStr) -> Self {
    Self { name }
  }

  pub fn label_name(&self) -> SmolStr {
    self.name.clone()
  }
}

impl InstructionNode {
  /// Creates an [InstructionNode] from the given instruction and operands
  pub fn from_operands(instruction: Instruction, operands: Vec<OperandNode>) -> Self {
    Self {
      instruction,
      operands,
    }
  }

  /// Creates an [InstructionNode] from the given instruction.
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

impl std::fmt::Display for OperandNode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      OperandNode::Identifier(ident) => write!(f, "{}", &ident),
      OperandNode::Register(reg) => write!(f, "{}", reg),
      OperandNode::Literal(num) => write!(f, "{}", num),
    }
  }
}

impl std::fmt::Display for LabelNode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", self.label_name())
  }
}

impl std::fmt::Display for ProgramNode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for node in self.children() {
      match node {
        Node::Instruction(inst_node) => {
          write!(f, "{}", inst_node.instruction())?;

          let op_count = inst_node.operands().len();

          // There are only at most 2 valid operands for instructions
          if op_count == 2 {
            writeln!(
              f,
              " {}, {}",
              inst_node.operands.first().unwrap(),
              inst_node.operands.get(1).unwrap()
            )?;
          } else if op_count == 1 {
            writeln!(f, " {}", inst_node.operands.first().unwrap(),)?;
          } else {
            writeln!(f)?;
          }
        }
        Node::Label(label) => {
          writeln!(f, "{}", label)?;
        }
      }
    }

    Ok(())
  }
}
