use crate::registers::Registers;
use crate::{encodings, registers::RegisterPair};
use lexer::directive::Directive;
use lexer::{instruction::Instruction, Flags, Register};
use parser::nodes::{
  DirectiveNode, Expression, ExpressionNode, InstructionNode, Operand, OperandNode, Operator,
};
use smol_str::SmolStr;
use types::{AssembleError, AssembleErrorKind, AssembleResult};

use std::collections::HashMap;

#[derive(Debug)]
pub struct Environment {
  pub flags: u8,
  pub registers: Registers,
  // Maps a program counter to a label
  pub label_indices: HashMap<u16, SmolStr>,
  // Maps a label to its address in the program
  pub labels: HashMap<SmolStr, u16>,
  pub memory: Box<[u8; Environment::MEMORY_SIZE]>,

  pub(crate) assemble_index: u16,
}

/// The size of an operand.
#[derive(Copy, Clone, Debug)]
enum OperandType {
  /// An 8-bit value.
  Byte,
  /// A 16-bit value.
  Word,
}

impl Environment {
  /// The default starting address of where instructions get encoded.
  pub const INSTRUCTION_STARTING_ADDRESS: u16 = 0x0000;

  /// The amount of memory available, which is 2^16.
  pub const MEMORY_SIZE: usize = u16::MAX as usize + 1;

  pub fn new() -> Self {
    Self::default()
  }

  /// The index used for assembling the data into memory.
  pub const fn assemble_index(&self) -> u16 {
    self.assemble_index
  }

  /// Returns true if the flags are set.
  pub fn is_flag_set(&self, f: Flags) -> bool {
    (self.flags & f as u8) == f as u8
  }

  /// Toggles the flags, depending on the `condition`.
  pub fn set_flag(&mut self, flag: Flags, condition: bool) {
    if condition {
      self.flags |= flag as u8;
    } else {
      self.flags &= !(flag as u8);
    }
  }

  /// Updates the flags after running an arithmetic instruction.
  pub fn update_flags_arithmetic(&mut self, old_value: u8, new_value: u8, is_addition: bool) {
    self.set_flag(Flags::Sign, new_value >> 7 == 1);
    self.set_flag(Flags::Zero, new_value == 0);
    self.set_flag(Flags::Parity, new_value.count_ones() % 2 == 0);

    let old_nibble = old_value & 0x0F;
    let new_nibble = new_value & 0x0F;

    if is_addition {
      self.set_flag(Flags::AuxiliaryCarry, old_nibble + new_nibble > 0x0F);
      // If we added, then we have a carry if the new value is smaller
      self.set_flag(Flags::Carry, new_value < old_value);
    } else {
      self.set_flag(Flags::AuxiliaryCarry, old_nibble < new_nibble);
      // If we subtracted, then we have a carry if the new value is greater
      self.set_flag(Flags::Carry, new_value > old_value);
    }
  }

  /// Updates the flags after running a logical instruction.
  /// This function indefinitely resets [`Flags::AuxiliaryCarry`] and [`Flags::Carry`].
  pub fn update_flags_logical(&mut self, value: u8) {
    self.set_flag(Flags::Sign, value >> 7 == 1);
    self.set_flag(Flags::Zero, value == 0);
    self.set_flag(Flags::Parity, value.count_ones() % 2 == 0);
    self.set_flag(Flags::Carry, false);
    self.set_flag(Flags::AuxiliaryCarry, false);
  }

  /// Writes a u16 onto the stack, writing the upper byte first.
  pub fn write_stack_u16(&mut self, address: u16) {
    // 8085 stores stuff in little endian, so the high byte should be stored first on the stack
    self.write_stack_u8((address >> 8) as u8);
    self.write_stack_u8((address & 0xFF) as u8);
  }

  /// Writes the byte onto the stack.
  pub fn write_stack_u8(&mut self, value: u8) {
    self.registers.sp = self.registers.sp.wrapping_sub(1);

    self.write_memory(self.registers.sp, value);
  }

  /// Writes the byte to the address.
  pub fn write_memory(&mut self, address: u16, value: u8) {
    *self.memory.get_mut(address as usize).unwrap() = value;
  }

  /// Reads a u16 from the stack, in little endian order.
  pub fn read_stack_u16(&mut self) -> u16 {
    let lower = self.read_stack_u8();
    let upper = self.read_stack_u8();

    (upper as u16) << 8 | lower as u16
  }

  /// Reads a byte from the stack.
  pub fn read_stack_u8(&mut self) -> u8 {
    let value = self.memory_at(self.registers.sp);

    self.registers.sp = self.registers.sp.wrapping_add(1);

    value
  }

  /// Reads the next byte of memory, wrapping the program counter if necessary.
  pub fn read_memory(&mut self) -> u8 {
    self.registers.pc = self.registers.pc.wrapping_add(1);

    self
      .memory
      .get(self.registers.pc as usize)
      .copied()
      .unwrap()
  }

  /// Reads a u16 from memory in little endian, wrapping the program counter if necessary.
  pub fn read_memory_u16(&mut self) -> u16 {
    let lower = self.read_memory();
    let upper = self.read_memory();

    (upper as u16) << 8 | lower as u16
  }

  /// Reads the byte of memory located at the address.
  pub fn memory_at(&self, address: u16) -> u8 {
    self.memory.get(address as usize).copied().unwrap()
  }

  /// Reads a register pair, with the first register being stored in the upper byte.
  pub fn read_register_pair(&self, reg_pair: RegisterPair) -> u16 {
    match reg_pair {
      RegisterPair::BC => (self.registers.b as u16) << 8 | self.registers.c as u16,
      RegisterPair::DE => (self.registers.d as u16) << 8 | self.registers.e as u16,
      RegisterPair::HL => (self.registers.h as u16) << 8 | self.registers.l as u16,
      RegisterPair::SP => self.registers.sp,
      RegisterPair::PSW => (self.registers.a as u16) << 8 | self.flags as u16,
    }
  }

  /// Writes to a register pair, storing the upper byte in the first register.
  pub fn write_register_pair(&mut self, reg_pair: RegisterPair, value: u16) {
    match reg_pair {
      RegisterPair::BC => {
        self.registers.b = (value >> 8) as u8;
        self.registers.c = (value & 0xFF) as u8;
      }
      RegisterPair::DE => {
        self.registers.d = (value >> 8) as u8;
        self.registers.e = (value & 0xFF) as u8;
      }
      RegisterPair::HL => {
        self.registers.h = (value >> 8) as u8;
        self.registers.l = (value & 0xFF) as u8;
      }
      RegisterPair::SP => {
        self.registers.sp = value;
      }
      RegisterPair::PSW => {
        self.registers.a = (value >> 8) as u8;
        self.flags = (value & 0xFF) as u8;
      }
    }
  }

  /// Sets the value of the register.
  ///
  /// If the register is [`Register::M`], then the value at the memory address
  /// of register pair H-L will be set.
  pub fn set_register_value(&mut self, dest_reg: Register, value: u8) {
    match dest_reg {
      Register::A => self.registers.a = value,
      Register::B => self.registers.b = value,
      Register::C => self.registers.c = value,
      Register::D => self.registers.d = value,
      Register::E => self.registers.e = value,
      Register::H => self.registers.h = value,
      Register::L => self.registers.l = value,

      Register::M => self.write_memory(
        (self.registers.h as u16) << 8 | self.registers.l as u16,
        value,
      ),
      _ => unreachable!(),
    }
  }

  /// Reads the value of the register.
  ///
  /// If the register is [`Register::M`], then the value at the memory address
  /// of register pair H-L is returned.
  pub fn get_register_value(&mut self, reg: Register) -> Option<u8> {
    Some(match reg {
      Register::A => self.registers.a,
      Register::B => self.registers.b,
      Register::C => self.registers.c,
      Register::D => self.registers.d,
      Register::E => self.registers.e,
      Register::H => self.registers.h,
      Register::L => self.registers.l,
      Register::M => self.memory_at((self.registers.h as u16) << 8 | self.registers.l as u16),
      _ => unreachable!(),
    })
  }

  /// Gets the start of a label from its name
  pub fn get_label_address(&self, label_name: &SmolStr) -> Option<u16> {
    self.labels.get(label_name).copied()
  }

  pub fn add_label(&mut self, label: SmolStr, addr: u16) {
    self.labels.insert(label, addr);
  }

  /// Assembles the following byte at the specified memory address.
  pub fn assemble_u8(&mut self, address: u16, byte: u8) {
    *self.memory.get_mut(address as usize).unwrap() = byte;
  }

  /// Assembles the 16-bit data at the specified memory address, in little endian order.
  pub fn assemble_u16(&mut self, address: u16, data: u16) {
    // Intel 8085 uses little endian, so store the low byte first
    self.assemble_u8(address, (data & 0xFF) as u8);
    self.assemble_u8(address + 1, (data >> 8) as u8);
  }

  /// Resets the flags, registers, and memory.
  ///
  /// The `starting_memory_index` is used to choose where to start clearing the memory from
  pub fn reset(&mut self, starting_memory_index: u16) {
    self.flags = Flags::NONE;
    self.registers = Registers::default();
    // Reuse the underlying allocation
    self.labels.clear();
    self.label_indices.clear();
    self.memory[starting_memory_index as usize..].fill(0);
  }

  /// Encodes a [`DirectiveNode`].
  pub fn encode_directive<'a>(
    &mut self,
    directive_node: &'a DirectiveNode,
    symbols: &mut HashMap<&'a SmolStr, u16>,
  ) -> AssembleResult<()> {
    match (directive_node.directive(), directive_node.operands()) {
      (
        Directive::EQU,
        &[OperandNode {
          operand: Operand::Numeric(data),
          ref span,
        }],
      ) => {
        if let Some(name) = directive_node.identifier() {
          if symbols.contains_key(name) {
            return Err(AssembleError::new(
              span.start,
              AssembleErrorKind::IdentifierAlreadyDefined,
            ));
          }

          symbols.insert(name, data);
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::DirectiveRequiresName,
          ));
        }
      }
      (Directive::EQU, _) => {
        return Err(AssembleError::new(
          directive_node.span().start,
          AssembleErrorKind::ExpectedTwoByteValue,
        ))
      }
      (
        Directive::SET,
        &[OperandNode {
          operand: Operand::Numeric(data),
          ref span,
        }],
      ) => {
        if let Some(name) = directive_node.identifier() {
          symbols.insert(name, data);
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::DirectiveRequiresName,
          ));
        }
      }
      (Directive::SET, ops) => {
        if ops.is_empty() {
          return Err(AssembleError::new(
            directive_node.span().start,
            AssembleErrorKind::DirectiveRequiresOperands,
          ));
        }

        return Err(AssembleError::new(
          directive_node.span().start,
          AssembleErrorKind::ExpectedTwoByteValue,
        ));
      }

      (Directive::DB, ops) => {
        if ops.is_empty() {
          return Err(AssembleError::new(
            directive_node.span().start,
            AssembleErrorKind::DirectiveRequiresOperands,
          ));
        }

        for op in ops {
          let res = match &op.operand {
            Operand::Numeric(num) => evaluate_directive_expression(
              self,
              &ExpressionNode::new(Expression::Number(*num), op.span.clone()),
              symbols,
              OperandType::Byte,
            ),
            Operand::Identifier(str) => evaluate_directive_expression(
              self,
              &ExpressionNode::new(Expression::Identifier(str.clone()), op.span.clone()),
              symbols,
              OperandType::Byte,
            ),
            Operand::String(str) => evaluate_directive_expression(
              self,
              &ExpressionNode::new(Expression::String(str.clone()), op.span.clone()),
              symbols,
              OperandType::Byte,
            ),
            Operand::Expression(expr) => {
              evaluate_directive_expression(self, expr, symbols, OperandType::Byte)
            }
            Operand::Register(_) => Err(AssembleError::new(
              op.span.start,
              AssembleErrorKind::InvalidOperandType,
            )),
          }?;

          if let Some(data) = res {
            self.assemble_u8(self.assemble_index, (data & 0xFF) as u8);
            self.assemble_index += 1;
          }
        }
      }

      (Directive::DW, ops) => {
        if ops.is_empty() {
          return Err(AssembleError::new(
            directive_node.span().start,
            AssembleErrorKind::DirectiveRequiresOperands,
          ));
        }

        for op in ops {
          let res = match &op.operand {
            Operand::Numeric(num) => evaluate_directive_expression(
              self,
              &ExpressionNode::new(Expression::Number(*num), op.span.clone()),
              symbols,
              OperandType::Word,
            ),
            Operand::Identifier(str) => evaluate_directive_expression(
              self,
              &ExpressionNode::new(Expression::Identifier(str.clone()), op.span.clone()),
              symbols,
              OperandType::Word,
            ),
            Operand::String(str) => evaluate_directive_expression(
              self,
              &ExpressionNode::new(Expression::String(str.clone()), op.span.clone()),
              symbols,
              OperandType::Word,
            ),
            Operand::Expression(expr) => {
              evaluate_directive_expression(self, expr, symbols, OperandType::Word)
            }
            Operand::Register(_) => Err(AssembleError::new(
              op.span.start,
              AssembleErrorKind::InvalidOperandType,
            )),
          }?;

          if let Some(data) = res {
            self.assemble_u16(self.assemble_index, data);
            self.assemble_index += 2;
          }
        }
      }
      (Directive::DS, [op]) => {
        let free_space = match &op.operand {
          Operand::Numeric(num) => evaluate_instruction_expression(
            self,
            &ExpressionNode::new(Expression::Number(*num), op.span.clone()),
          ),
          Operand::Identifier(str) => evaluate_instruction_expression(
            self,
            &ExpressionNode::new(Expression::Identifier(str.clone()), op.span.clone()),
          ),
          Operand::String(str) => evaluate_instruction_expression(
            self,
            &ExpressionNode::new(Expression::String(str.clone()), op.span.clone()),
          ),
          Operand::Expression(expr) => evaluate_instruction_expression(self, expr),
          Operand::Register(_) => Err(AssembleError::new(
            op.span.start,
            AssembleErrorKind::InvalidOperandType,
          )),
        }?;

        self.assemble_index += free_space;
      }
      (Directive::DS, _) => {
        return Err(AssembleError::new(
          directive_node.span().start,
          AssembleErrorKind::ExpectedTwoByteValue,
        ));
      }
      _ => unreachable!(),
    }

    Ok(())
  }

  /// Encodes the [`InstructionNode`] into the specified spot in memory.
  ///
  /// If it was unable to be encoded, due to the label's address not known at
  /// the time, there will need to be a second pass at encoding.
  pub fn encode_instruction<'a>(
    &mut self,
    assemble_index: u16,
    instruction_node: &'a InstructionNode,
    unassembled: &mut Vec<(&'a InstructionNode, u16)>,
    recoding: bool,
  ) -> AssembleResult<()> {
    use Instruction::*;

    let addr = Self::INSTRUCTION_STARTING_ADDRESS + assemble_index;

    match (instruction_node.instruction(), instruction_node.operands()) {
      // Register, Register operands
      (
        MOV,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::Register(r2),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encode_mov(r1, r2));
      }
      (
        MOV,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }, OperandNode {
          operand: ref op2,
          span: ref sp2,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        } else if !matches!(op2, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp2.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }

      // Register, d16 operands
      (
        LXI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::Numeric(data),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encode_lxi(r1));
        self.assemble_u16(addr + 1, data);
      }
      (
        LXI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::Identifier(ref label),
          ref span,
        }],
      ) => {
        if label == "$" {
          self.assemble_u8(addr, encode_lxi(r1));
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(label_addr) = self.get_label_address(label) {
          self.assemble_u8(addr, encode_lxi(r1));
          self.assemble_u16(addr + 1, label_addr);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        LXI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::String(ref str),
          ref span,
        }],
      ) => {
        if str.len() == 2 {
          let bytes = str.as_bytes();
          let data = (bytes[0] as u16) << 8 | bytes[1] as u16;

          self.assemble_u8(addr, encode_lxi(r1));
          self.assemble_u16(addr + 1, data);
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedTwoByteValue,
          ));
        }
      }
      (
        LXI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let res = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encode_lxi(r1));
        self.assemble_u16(addr + 1, res);
      }
      (
        LXI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }, OperandNode {
          operand: ref op2,
          span: ref sp2,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        } else if !matches!(
          op2,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp2.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }

      // Register, d8 operands
      (
        MVI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::Numeric(data),
          ref span,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encode_mvi(r1));
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        MVI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::String(ref data),
          ref span,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encode_mvi(r1));
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        MVI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encode_mvi(r1));
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
      },
      (
        MVI,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }, OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encode_mvi(r1));
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        MVI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }, OperandNode {
          operand: ref op2,
          span: ref sp2,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        } else if !matches!(
          op2,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp2.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }

      // Register operands
      (
        LDAX,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_ldax(r1)),
      (
        LDAX,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        STAX,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_stax(r1)),
      (
        STAX,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        INX,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_inx(r1)),
      (
        INX,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        DCX,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_dcx(r1)),
      (
        DCX,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        POP,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_pop(r1)),
      (
        POP,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        PUSH,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_push(r1)),
      (
        PUSH,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        DAD,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_dad(r1)),
      (
        DAD,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        ADD,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_add(r1)),
      (
        ADD,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        ADC,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_adc(r1)),
      (
        ADC,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        SUB,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_sub(r1)),
      (
        SUB,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        SBB,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_sbb(r1)),
      (
        SBB,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        ANA,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_ana(r1)),
      (
        ANA,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        XRA,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_xra(r1)),
      (
        XRA,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        ORA,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_ora(r1)),
      (
        ORA,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CMP,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_cmp(r1)),
      (
        CMP,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        INR,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_inr(r1)),
      (
        INR,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        DCR,
        &[OperandNode {
          operand: Operand::Register(r1),
          ..
        }],
      ) => self.assemble_u8(addr, encode_dcr(r1)),
      (
        DCR,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(op1, Operand::Register(_)) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }

      // a16 operands
      (
        JNZ,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JNZ);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JNZ);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JNZ,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JNZ);
        self.assemble_u16(addr + 1, num);
      }
      (
        JNZ,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JNZ);
        self.assemble_u16(addr + 1, val);
      }
      (
        JNZ,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JNC,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JNC);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JNC);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JNC,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JNC);
        self.assemble_u16(addr + 1, val);
      }
      (
        JNC,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JPO,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JPO);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JPO);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JPO,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JPO);
        self.assemble_u16(addr + 1, num);
      }
      (
        JPO,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JPO);
        self.assemble_u16(addr + 1, val);
      }
      (
        JPO,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JP,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JP);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JP);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JP,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JP);
        self.assemble_u16(addr + 1, num);
      }
      (
        JP,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JP);
        self.assemble_u16(addr + 1, val);
      }
      (
        JP,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JMP,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JMP);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JMP);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JMP,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JMP);
        self.assemble_u16(addr + 1, num);
      }
      (
        JMP,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JMP);
        self.assemble_u16(addr + 1, val);
      }
      (
        JMP,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JZ,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JZ);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JZ);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JZ,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JZ);
        self.assemble_u16(addr + 1, num);
      }
      (
        JZ,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JZ);
        self.assemble_u16(addr + 1, val);
      }
      (
        JZ,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JC,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JC);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JC);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JC,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JC);
        self.assemble_u16(addr + 1, num);
      }
      (
        JC,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JC);
        self.assemble_u16(addr + 1, val);
      }
      (
        JC,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JPE,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JPE);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JPE);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JPE,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JPE);
        self.assemble_u16(addr + 1, num);
      }
      (
        JPE,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JPE);
        self.assemble_u16(addr + 1, val);
      }
      (
        JPE,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        JM,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::JM);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::JM);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        JM,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::JM);
        self.assemble_u16(addr + 1, num);
      }
      (
        JM,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::JM);
        self.assemble_u16(addr + 1, val);
      }
      (
        JM,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CNZ,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CNZ);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CNZ);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CNZ,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CNZ);
        self.assemble_u16(addr + 1, num);
      }
      (
        CNZ,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CNZ);
        self.assemble_u16(addr + 1, val);
      }
      (
        CNZ,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CNC,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CNC);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CNC);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CNC,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CNC);
        self.assemble_u16(addr + 1, num);
      }
      (
        CNC,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CNC);
        self.assemble_u16(addr + 1, val);
      }
      (
        CNC,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CPO,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CPO);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CPO);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CPO,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CPO);
        self.assemble_u16(addr + 1, num);
      }
      (
        CPO,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CPO);
        self.assemble_u16(addr + 1, val);
      }
      (
        CPO,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CP,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CP);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CP);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CP,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CP);
        self.assemble_u16(addr + 1, num);
      }
      (
        CP,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CP);
        self.assemble_u16(addr + 1, val);
      }
      (
        CP,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CZ,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CZ);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CZ);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CZ,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CZ);
        self.assemble_u16(addr + 1, num);
      }
      (
        CZ,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CZ);
        self.assemble_u16(addr + 1, val);
      }
      (
        CZ,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CC,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CC);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CC);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CC,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CC);
        self.assemble_u16(addr + 1, num);
      }
      (
        CC,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CC);
        self.assemble_u16(addr + 1, val);
      }
      (
        CC,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CPE,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CPE);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CPE);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CPE,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CPE);
        self.assemble_u16(addr + 1, num);
      }
      (
        CPE,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CPE);
        self.assemble_u16(addr + 1, val);
      }
      (
        CPE,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CM,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CM);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CM);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CM,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CM);
        self.assemble_u16(addr + 1, num);
      }
      (
        CM,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CM);
        self.assemble_u16(addr + 1, val);
      }
      (
        CM,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        CALL,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::CALL);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(jmp_to) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::CALL);
          self.assemble_u16(addr + 1, jmp_to);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        CALL,
        &[OperandNode {
          operand: Operand::Numeric(num),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::CALL);
        self.assemble_u16(addr + 1, num);
      }
      (
        CALL,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::CALL);
        self.assemble_u16(addr + 1, val);
      }
      (
        CALL,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        STA,
        &[OperandNode {
          operand: Operand::Numeric(data),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::STA);
        self.assemble_u16(addr + 1, data);
      }
      (
        STA,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::STA);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(label_addr) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::STA);
          self.assemble_u16(addr + 1, label_addr);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        STA,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let res = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::STA);
        self.assemble_u16(addr + 1, res);
      }
      (
        STA,
        &[OperandNode {
          operand: ref op1,
          span: ref sp2,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp2.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        SHLD,
        &[OperandNode {
          operand: Operand::Numeric(data),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::SHLD);
        self.assemble_u16(addr + 1, data);
      }

      (
        SHLD,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::SHLD);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(label_addr) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::SHLD);
          self.assemble_u16(addr + 1, label_addr);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        SHLD,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let res = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::SHLD);
        self.assemble_u16(addr + 1, res);
      }
      (
        SHLD,
        &[OperandNode {
          operand: ref op1,
          span: ref sp2,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp2.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        LDA,
        &[OperandNode {
          operand: Operand::Numeric(data),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::LDA);
        self.assemble_u16(addr + 1, data);
      }
      (
        LDA,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::LDA);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(label_addr) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::LDA);
          self.assemble_u16(addr + 1, label_addr);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        LDA,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let res = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::LDA);
        self.assemble_u16(addr + 1, res);
      }
      (
        LDA,
        &[OperandNode {
          operand: ref op1,
          span: ref sp2,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp2.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        LHLD,
        &[OperandNode {
          operand: Operand::Numeric(data),
          ..
        }],
      ) => {
        self.assemble_u8(addr, encodings::LHLD);
        self.assemble_u16(addr + 1, data);
      }
      (
        LHLD,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => {
        if ident == "$" {
          self.assemble_u8(addr, encodings::LHLD);
          self.assemble_u16(addr + 1, self.assemble_index);
        } else if let Some(label_addr) = self.get_label_address(ident) {
          self.assemble_u8(addr, encodings::LHLD);
          self.assemble_u16(addr + 1, label_addr);
        } else if !recoding {
          unassembled.push((instruction_node, addr));
        } else {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ));
        }
      }
      (
        LHLD,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ..
        }],
      ) => {
        let res = evaluate_instruction_expression(self, expr)?;

        self.assemble_u8(addr, encodings::LHLD);
        self.assemble_u16(addr + 1, res);
      }
      (
        LHLD,
        &[OperandNode {
          operand: ref op1,
          span: ref sp2,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_) | Operand::Identifier(_) | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp2.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }

      // d8 operands
      (
        ACI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > 0xFF {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ACI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        ACI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::ACI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        ACI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::ACI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        ACI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ACI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        SBI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::SBI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        SBI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::SBI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        SBI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::SBI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        SBI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::SBI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        SBI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_),
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        XRI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::XRI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        XRI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::XRI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        XRI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::XRI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        XRI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::XRI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        XRI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_)
            | Operand::String(_)
            | Operand::Identifier(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        CPI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::CPI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        CPI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::CPI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        CPI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::CPI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        CPI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::CPI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        CPI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        ADI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ADI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        ADI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::ADI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        ADI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::ADI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        ADI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ADI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        ADI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        SUI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::SUI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        SUI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::SUI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        SUI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::SUI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        SUI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::SUI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        SUI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        ANI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ANI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        ANI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::ANI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        ANI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::ANI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        ANI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ANI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        ANI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }
      (
        ORI,
        &[OperandNode {
          operand: Operand::Numeric(data),
          span: ref sp1,
        }],
      ) => {
        if data > u8::MAX as u16 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ORI);
        self.assemble_u8(addr + 1, (data & 0xFF) as u8);
      }
      (
        ORI,
        &[OperandNode {
          operand: Operand::String(ref data),
          span: ref sp1,
        }],
      ) => {
        if data.len() == 1 {
          self.assemble_u8(addr, encodings::ORI);
          self.assemble_u8(addr + 1, data.as_bytes()[0]);
        } else {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }
      }
      (
        ORI,
        &[OperandNode {
          operand: Operand::Identifier(ref ident),
          ref span,
        }],
      ) => match self.get_label_address(ident) {
        Some(addr) if addr <= u8::MAX as u16 => {
          self.assemble_u8(addr, encodings::ORI);
          self.assemble_u8(addr + 1, addr as u8);
        }
        Some(_) => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ))
        }
        None if recoding => {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::IdentifierNotDefined,
          ))
        }
        None => {
          unassembled.push((instruction_node, addr));
        }
      },
      (
        ORI,
        &[OperandNode {
          operand: Operand::Expression(ref expr),
          ref span,
        }],
      ) => {
        let val = evaluate_instruction_expression(self, expr)?;

        if val > u8::MAX as u16 {
          return Err(AssembleError::new(
            span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        self.assemble_u8(addr, encodings::ORI);
        self.assemble_u8(addr + 1, val as u8);
      }
      (
        ORI,
        &[OperandNode {
          operand: ref op1,
          span: ref sp1,
        }],
      ) => {
        if !matches!(
          op1,
          Operand::Numeric(_)
            | Operand::Identifier(_)
            | Operand::String(_)
            | Operand::Expression(_)
        ) {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandType,
          ));
        }
      }

      // Special d8 operand that only takes a value between 0-8
      (
        RST,
        &[OperandNode {
          operand: Operand::Numeric(num),
          span: ref sp1,
        }],
      ) => {
        if num > 8 {
          return Err(AssembleError::new(
            sp1.start,
            AssembleErrorKind::InvalidOperandValue,
          ));
        }

        self.assemble_u8(addr, encode_rst(num as u8));
      }

      // No operands
      (RP, &[]) => self.assemble_u8(addr, encodings::RP),
      (RZ, &[]) => self.assemble_u8(addr, encodings::RZ),
      (RC, &[]) => self.assemble_u8(addr, encodings::RC),
      (RM, &[]) => self.assemble_u8(addr, encodings::RM),
      (RNZ, &[]) => self.assemble_u8(addr, encodings::RNZ),
      (RNC, &[]) => self.assemble_u8(addr, encodings::RNC),
      (RPO, &[]) => self.assemble_u8(addr, encodings::RPO),
      (RPE, &[]) => self.assemble_u8(addr, encodings::RPE),
      (RET, &[]) => self.assemble_u8(addr, encodings::RET),
      (RAL, &[]) => self.assemble_u8(addr, encodings::RAL),
      (RLC, &[]) => self.assemble_u8(addr, encodings::RLC),
      (RRC, &[]) => self.assemble_u8(addr, encodings::RRC),
      (RAR, &[]) => self.assemble_u8(addr, encodings::RAR),
      (CMA, &[]) => self.assemble_u8(addr, encodings::CMA),
      (CMC, &[]) => self.assemble_u8(addr, encodings::CMC),
      (SPHL, &[]) => self.assemble_u8(addr, encodings::SPHL),
      (PCHL, &[]) => self.assemble_u8(addr, encodings::PCHL),
      (XCHG, &[]) => self.assemble_u8(addr, encodings::XCHG),
      (XTHL, &[]) => self.assemble_u8(addr, encodings::XTHL),
      (STC, &[]) => self.assemble_u8(addr, encodings::STC),
      (DAA, &[]) => self.assemble_u8(addr, encodings::DAA),
      (NOP, &[]) => self.assemble_u8(addr, encodings::NOP),
      (HLT, &[]) => self.assemble_u8(addr, encodings::HLT),

      (instruction, _) => panic!("missing case when assembling {instruction}"),
    }

    self.assemble_index += instruction_bytes_occupied(instruction_node.instruction()) as u16;

    Ok(())
  }
}

impl Default for Environment {
  fn default() -> Self {
    Self {
      flags: Flags::NONE,
      registers: Registers::default(),
      label_indices: HashMap::new(),
      labels: HashMap::new(),
      memory: Box::new([0; Environment::MEMORY_SIZE]),
      assemble_index: 0,
    }
  }
}

/// Evaluates an expression in an instruction.
fn evaluate_instruction_expression(
  env: &Environment,
  expr: &ExpressionNode,
) -> AssembleResult<u16> {
  match expr.value() {
    Expression::Number(num) => Ok(*num),
    Expression::String(str) => {
      if str.len() == 2 {
        let bytes = str.as_bytes();

        Ok(((bytes[0] as u16) << 8) | bytes[1] as u16)
      } else {
        Err(AssembleError::new(
          expr.span.start,
          AssembleErrorKind::ExpectedTwoByteValue,
        ))
      }
    }
    Expression::Identifier(ref label) => {
      if label == "$" {
        Ok(env.assemble_index)
      } else {
        match env.get_label_address(label) {
          Some(addr) => Ok(addr),
          None => Err(AssembleError::new(
            expr.span.start,
            AssembleErrorKind::IdentifierNotDefined,
          )),
        }
      }
    }
    Expression::Paren(child_expr) => evaluate_instruction_expression(env, child_expr),
    Expression::Unary {
      op,
      expr: child_expr,
    } => match op {
      Operator::Addition => evaluate_instruction_expression(env, child_expr),
      // Handle unary subtraction via wraparound
      Operator::Subtraction => {
        Ok(0_u16.wrapping_sub(evaluate_instruction_expression(env, child_expr)?))
      }
      Operator::High => Ok(evaluate_instruction_expression(env, child_expr)? >> 8),
      Operator::Low => Ok(evaluate_instruction_expression(env, child_expr)? & 0xFF),
      Operator::Not => Ok(!evaluate_instruction_expression(env, child_expr)?),
      _ => unreachable!(),
    },
    Expression::Binary { op, left, right } => match op {
      Operator::Addition => Ok(
        evaluate_instruction_expression(env, left)?
          .wrapping_add(evaluate_instruction_expression(env, right)?),
      ),
      Operator::Subtraction => Ok(
        evaluate_instruction_expression(env, left)?
          .wrapping_sub(evaluate_instruction_expression(env, right)?),
      ),
      Operator::Division => Ok(
        evaluate_instruction_expression(env, left)?
          .wrapping_div(evaluate_instruction_expression(env, right)?),
      ),
      Operator::Multiplication => Ok(
        evaluate_instruction_expression(env, left)?
          .wrapping_mul(evaluate_instruction_expression(env, right)?),
      ),

      Operator::Modulo => Ok(
        evaluate_instruction_expression(env, left)? % evaluate_instruction_expression(env, right)?,
      ),
      Operator::ShiftLeft => Ok(
        evaluate_instruction_expression(env, left)?
          .wrapping_shl(evaluate_instruction_expression(env, right)? as u32),
      ),
      Operator::ShiftRight => Ok(
        evaluate_instruction_expression(env, left)?
          .wrapping_shr(evaluate_instruction_expression(env, right)? as u32),
      ),
      Operator::And => Ok(
        evaluate_instruction_expression(env, left)? & evaluate_instruction_expression(env, right)?,
      ),
      Operator::Or => Ok(
        evaluate_instruction_expression(env, left)? | evaluate_instruction_expression(env, right)?,
      ),
      Operator::Xor => Ok(
        evaluate_instruction_expression(env, left)? ^ evaluate_instruction_expression(env, right)?,
      ),

      Operator::Eq => Ok(
        (evaluate_instruction_expression(env, left)?
          == evaluate_instruction_expression(env, right)?) as u16,
      ),
      Operator::Ne => Ok(
        (evaluate_instruction_expression(env, left)?
          != evaluate_instruction_expression(env, right)?) as u16,
      ),
      // NOTE: Relational comparisons compare the bits, not the values
      Operator::Lt => Ok(
        (evaluate_instruction_expression(env, left)? < evaluate_instruction_expression(env, right)?)
          as u16,
      ),
      Operator::Le => Ok(
        (evaluate_instruction_expression(env, left)?
          <= evaluate_instruction_expression(env, right)?) as u16,
      ),
      Operator::Gt => Ok(
        (evaluate_instruction_expression(env, left)? > evaluate_instruction_expression(env, right)?)
          as u16,
      ),
      Operator::Ge => Ok(
        (evaluate_instruction_expression(env, left)?
          >= evaluate_instruction_expression(env, right)?) as u16,
      ),
      // `NOT`, `HIGH`, `LOW `are handled in the unary section
      Operator::Not | Operator::High | Operator::Low => unreachable!(),
    },
  }
}

/// Evalutes an expression from a directive.
///
/// The result returns `None` if it encoded the bytes into memory.
fn evaluate_directive_expression(
  env: &mut Environment,
  expr: &ExpressionNode,
  symbols: &HashMap<&SmolStr, u16>,
  operand_type: OperandType,
) -> AssembleResult<Option<u16>> {
  let arithmetic_string_handler = |node: &ExpressionNode| -> AssembleResult<()> {
    // Arithmetic operators aren't that well defined for strings
    match operand_type {
      OperandType::Byte if matches!(node.value(), Expression::String(s) if s.len() > 1) => Err(
        AssembleError::new(expr.span.start, AssembleErrorKind::InvalidOperator),
      ),
      OperandType::Word if matches!(node.value(), Expression::String(s) if s.len() > 2) => Err(
        AssembleError::new(expr.span.start, AssembleErrorKind::InvalidOperator),
      ),
      _ => Ok(()),
    }
  };

  match expr.value() {
    Expression::Number(num) => {
      if matches!(operand_type, OperandType::Byte) && *num > u8::MAX as u16 {
        return Err(AssembleError::new(
          expr.span.start,
          AssembleErrorKind::ExpectedOneByteValue,
        ));
      }

      Ok(Some(*num))
    }
    Expression::String(str) => {
      if str.is_empty() {
        return Err(AssembleError::new(
          expr.span.start,
          AssembleErrorKind::ExpectedValue,
        ));
      }

      match operand_type {
        OperandType::Byte => {
          for &byte in str.as_bytes() {
            env.assemble_u8(env.assemble_index, byte);
            env.assemble_index += 1;
          }

          Ok(None)
        }
        OperandType::Word => {
          if str.len() > 2 {
            return Err(AssembleError::new(
              expr.span.start,
              AssembleErrorKind::ExpectedTwoByteValue,
            ));
          }

          let bytes = str.as_bytes();
          Ok(Some(
            (bytes[0] as u16) << 8 | bytes.get(1).copied().unwrap_or(0) as u16,
          ))
        }
      }
    }
    Expression::Identifier(ref ident) => {
      if ident == "$" {
        if matches!(operand_type, OperandType::Byte) && env.assemble_index > u8::MAX as u16 {
          return Err(AssembleError::new(
            expr.span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        Ok(Some(env.assemble_index))
      } else if let Some(symbol) = symbols.get(&ident) {
        if matches!(operand_type, OperandType::Byte) && *symbol > u8::MAX as u16 {
          return Err(AssembleError::new(
            expr.span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        Ok(Some(*symbol))
      } else if let Some(addr) = env.get_label_address(ident) {
        if matches!(operand_type, OperandType::Byte) && addr > u8::MAX as u16 {
          return Err(AssembleError::new(
            expr.span.start,
            AssembleErrorKind::ExpectedOneByteValue,
          ));
        }

        Ok(Some(addr))
      } else {
        Err(AssembleError::new(
          expr.span.start,
          AssembleErrorKind::IdentifierNotDefined,
        ))
      }
    }
    Expression::Paren(child_expr) => {
      evaluate_directive_expression(env, child_expr, symbols, operand_type)
    }
    Expression::Unary {
      op,
      expr: child_expr,
    } => match op {
      Operator::Addition => {
        arithmetic_string_handler(expr)?;

        evaluate_directive_expression(env, child_expr, symbols, operand_type)
      }
      // Handle unary subtraction via wraparound
      Operator::Subtraction => {
        arithmetic_string_handler(expr)?;

        evaluate_directive_expression(env, child_expr, symbols, operand_type)
          .map(|x| x.map(|num| 0_u16.wrapping_sub(num)))
      }
      Operator::High => {
        arithmetic_string_handler(expr)?;

        evaluate_directive_expression(env, child_expr, symbols, operand_type)
          .map(|x| x.map(|num| num >> 8))
      }
      Operator::Low => {
        arithmetic_string_handler(expr)?;

        evaluate_directive_expression(env, child_expr, symbols, operand_type)
          .map(|x| x.map(|num| num & 0xFF))
      }
      Operator::Not => {
        arithmetic_string_handler(expr)?;

        evaluate_directive_expression(env, child_expr, symbols, operand_type)
          .map(|x| x.map(|num| !num))
      }
      _ => unreachable!(),
    },
    Expression::Binary { op, left, right } => {
      arithmetic_string_handler(left)?;
      arithmetic_string_handler(right)?;

      let mut do_arithmetic =
        |left: &ExpressionNode, right: &ExpressionNode| -> AssembleResult<Option<(u16, u16)>> {
          match (
            evaluate_directive_expression(env, left, symbols, operand_type),
            evaluate_directive_expression(env, right, symbols, operand_type),
          ) {
            (Ok(Some(x)), Ok(Some(y))) => Ok(Some((x, y))),
            (Ok(None), _) | (_, Ok(None)) => Ok(None),
            (Err(e), _) | (_, Err(e)) => Err(e),
          }
        };

      match op {
        Operator::Addition => {
          do_arithmetic(left, right).map(|res| res.map(|(x, y)| x.wrapping_add(y)))
        }
        Operator::Subtraction => {
          do_arithmetic(left, right).map(|res| res.map(|(x, y)| x.wrapping_sub(y)))
        }
        Operator::Division => {
          do_arithmetic(left, right).map(|res| res.map(|(x, y)| x.wrapping_div(y)))
        }
        Operator::Multiplication => {
          do_arithmetic(left, right).map(|res| res.map(|(x, y)| x.wrapping_mul(y)))
        }
        Operator::Modulo => do_arithmetic(left, right).map(|res| res.map(|(x, y)| x % y)),
        Operator::ShiftLeft => {
          do_arithmetic(left, right).map(|res| res.map(|(x, y)| x.wrapping_shl(y as u32)))
        }
        Operator::ShiftRight => {
          do_arithmetic(left, right).map(|res| res.map(|(x, y)| x.wrapping_shr(y as u32)))
        }
        Operator::And => do_arithmetic(left, right).map(|res| res.map(|(x, y)| x & y)),
        Operator::Or => do_arithmetic(left, right).map(|res| res.map(|(x, y)| x | y)),
        Operator::Xor => do_arithmetic(left, right).map(|res| res.map(|(x, y)| x ^ y)),
        Operator::Eq => do_arithmetic(left, right).map(|res| res.map(|(x, y)| (x == y) as u16)),
        Operator::Ne => do_arithmetic(left, right).map(|res| res.map(|(x, y)| (x != y) as u16)),

        // NOTE: Relational comparisons compare the bits, not the values
        Operator::Lt => do_arithmetic(left, right).map(|res| res.map(|(x, y)| (x < y) as u16)),
        Operator::Le => do_arithmetic(left, right).map(|res| res.map(|(x, y)| (x <= y) as u16)),
        Operator::Gt => do_arithmetic(left, right).map(|res| res.map(|(x, y)| (x > y) as u16)),
        Operator::Ge => do_arithmetic(left, right).map(|res| res.map(|(x, y)| (x >= y) as u16)),
        // `NOT`, `HIGH`, `LOW `are handled in the unary section
        Operator::Not | Operator::High | Operator::Low => unreachable!(),
      }
    }
  }
}

const fn encode_rst(num: u8) -> u8 {
  // `RST` takes the form 0b11`XXX`111, where `XXX `are the encoded bits
  0b11000111 | (num << 3)
}

const fn encode_push(r1: Register) -> u8 {
  let encoded_rp = match r1 {
    Register::B => 0b00,
    Register::D => 0b01,
    Register::H => 0b10,
    Register::PSW => 0b11,
    _ => unreachable!(),
  };

  // `PUSH` takes the form 0b11`RP`0101, where `RP` is the register pair
  0b11000101 | (encoded_rp << 4)
}

const fn encode_pop(r1: Register) -> u8 {
  let encoded_rp = match r1 {
    Register::B => 0b00,
    Register::D => 0b01,
    Register::H => 0b10,
    Register::PSW => 0b11,
    _ => unreachable!(),
  };

  // `POP` takes the form 0b11`RP`0001, where `RP` is the register pair
  0b11000001 | (encoded_rp << 4)
}

const fn encode_dcx(r1: Register) -> u8 {
  let encoded_rp = match r1 {
    Register::B => 0b00,
    Register::D => 0b01,
    Register::H => 0b10,
    Register::SP => 0b11,
    _ => unreachable!(),
  };

  // `DCX` takes the form 0b00`RP`1011, where `RP` is the register pair
  0b00001011 | (encoded_rp << 4)
}

const fn encode_dad(r1: Register) -> u8 {
  let encoded_rp = match r1 {
    Register::B => 0b00,
    Register::D => 0b01,
    Register::H => 0b10,
    Register::SP => 0b11,
    _ => unreachable!(),
  };

  // `DAD` takes the form 0b00`RP`1001, where `RP` is the register pair
  0b00001001 | (encoded_rp << 4)
}

const fn encode_inx(r1: Register) -> u8 {
  let encoded_rp = match r1 {
    Register::B => 0b00,
    Register::D => 0b01,
    Register::H => 0b10,
    Register::SP => 0b11,
    _ => unreachable!(),
  };

  // `INX` takes the form 0b00`RP`0011, where `RP` is the register pair
  0b00000011 | (encoded_rp << 4)
}

const fn encode_lxi(r1: Register) -> u8 {
  let encoded_rp = match r1 {
    Register::B => 0b00,
    Register::D => 0b01,
    Register::H => 0b10,
    Register::SP => 0b11,
    _ => unreachable!(),
  };

  // `LXI` takes the form 0b00`RP`0001, where `RP` is the register pair
  0b00000001 | (encoded_rp << 4)
}

const fn encode_mov(r1: Register, r2: Register) -> u8 {
  // `MOV` takes the form of 0b01`XXX``YYY` where `XXX` is the dest and `YYY` is the src
  0b01000000 | (encode_register(r1) << 3) | encode_register(r2)
}

const fn encode_mvi(r1: Register) -> u8 {
  // `MVI` takes the form of 0b00`XXX`110 where `XXX` is the register
  0b00000110 | (encode_register(r1) << 3)
}

const fn encode_dcr(r1: Register) -> u8 {
  // `DCR` takes the form of 0b00`XXX`101 where `XXX` is the register
  0b00000101 | (encode_register(r1) << 3)
}

const fn encode_inr(r1: Register) -> u8 {
  // `INR` takes the form of 0b00`XXX`100 where `XXX` is the register
  0b00000100 | (encode_register(r1) << 3)
}

const fn encode_add(r1: Register) -> u8 {
  // `ADD` takes the form of 0b10000`XXX` where `XXX` is the register
  0b10000000 | encode_register(r1)
}

const fn encode_adc(r1: Register) -> u8 {
  // `ADC` takes the form of 0b10001`XXX` where `XXX` is the register
  0b10001000 | encode_register(r1)
}

const fn encode_sub(r1: Register) -> u8 {
  // `SUB` takes the form of 0b10010`XXX` where `XXX` is the register
  0b10010000 | encode_register(r1)
}

const fn encode_sbb(r1: Register) -> u8 {
  // `SBB` takes the form of 0b10011`XXX` where `XXX` is the register
  0b10011000 | encode_register(r1)
}

const fn encode_ana(r1: Register) -> u8 {
  // `ANA` takes the form of 0b10100`XXX` where `XXX` is the register
  0b10100000 | encode_register(r1)
}

const fn encode_xra(r1: Register) -> u8 {
  // `XRA` takes the form of 0b10101`XXX` where `XXX` is the register
  0b10101000 | encode_register(r1)
}

const fn encode_ora(r1: Register) -> u8 {
  // `ORA` takes the form of 0b10110`XXX` where `XXX` is the register
  0b10110000 | encode_register(r1)
}

const fn encode_cmp(r1: Register) -> u8 {
  // `CMP` takes the form of 0b10111`XXX` where `XXX` is the register
  0b10111000 | encode_register(r1)
}

const fn encode_register(r1: Register) -> u8 {
  match r1 {
    Register::B => 0,
    Register::C => 1,
    Register::D => 2,
    Register::E => 3,
    Register::H => 4,
    Register::L => 5,
    Register::M => 6,
    Register::A => 7,
    _ => unreachable!(),
  }
}

// NOTE: LDAX and STAX don't seem to follow an encoding pattern?
const fn encode_ldax(r1: Register) -> u8 {
  match r1 {
    Register::B => encodings::LDAX_B,
    Register::D => encodings::LDAX_D,
    _ => unreachable!(),
  }
}
const fn encode_stax(r1: Register) -> u8 {
  match r1 {
    Register::B => encodings::STAX_B,
    Register::D => encodings::STAX_D,
    _ => unreachable!(),
  }
}

/// Returns the number of bytes this instruction occupies in memory.
fn instruction_bytes_occupied(ins: Instruction) -> u8 {
  match ins {
    // 0 operand instructions
    Instruction::NOP => 1,
    Instruction::RAL => 1,
    Instruction::RLC => 1,
    Instruction::RRC => 1,
    Instruction::RAR => 1,
    Instruction::CMA => 1,
    Instruction::CMC => 1,
    Instruction::HLT => 1,
    Instruction::RNZ => 1,
    Instruction::RNC => 1,
    Instruction::RPO => 1,
    Instruction::RP => 1,
    Instruction::RZ => 1,
    Instruction::RC => 1,
    Instruction::RPE => 1,
    Instruction::RM => 1,
    Instruction::RET => 1,
    Instruction::XCHG => 1,
    Instruction::XTHL => 1,
    Instruction::SPHL => 1,
    Instruction::PCHL => 1,
    Instruction::STC => 1,
    Instruction::DAA => 1,
    // 1 operand instructions
    Instruction::ACI => 2,
    Instruction::SBI => 2,
    Instruction::XRI => 2,
    Instruction::CPI => 2,
    Instruction::ADD => 1,
    Instruction::ADI => 2,
    Instruction::SUI => 2,
    Instruction::ANI => 2,
    Instruction::ORI => 2,
    Instruction::ADC => 1,
    Instruction::SUB => 1,
    Instruction::SBB => 1,
    Instruction::ANA => 1,
    Instruction::XRA => 1,
    Instruction::ORA => 1,
    Instruction::CMP => 1,
    Instruction::INX => 1,
    Instruction::INR => 1,
    Instruction::DCR => 1,
    Instruction::DAD => 1,
    Instruction::DCX => 1,
    Instruction::POP => 1,
    Instruction::PUSH => 1,
    Instruction::STA => 3,
    Instruction::SHLD => 3,
    Instruction::STAX => 1,
    Instruction::LDA => 3,
    Instruction::LDAX => 1,
    Instruction::LHLD => 3,
    Instruction::JNZ => 3,
    Instruction::JNC => 3,
    Instruction::JPO => 3,
    Instruction::JP => 3,
    Instruction::JMP => 3,
    Instruction::JZ => 3,
    Instruction::JC => 3,
    Instruction::JPE => 3,
    Instruction::JM => 3,
    Instruction::CNZ => 3,
    Instruction::CNC => 3,
    Instruction::CPO => 3,
    Instruction::CP => 3,
    Instruction::CZ => 3,
    Instruction::CC => 3,
    Instruction::CPE => 3,
    Instruction::CM => 3,
    Instruction::CALL => 3,
    Instruction::RST => 1,
    // 2 operand instructions
    Instruction::LXI => 3,
    Instruction::MVI => 2,
    Instruction::MOV => 1,
  }
}
