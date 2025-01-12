use crate::encodings;
use crate::registers::Registers;
use lexer::{instruction::Instruction, Flags, Register};
use parser::nodes::{ExpressionNode, InstructionNode, OperandNode, Operator};
use smol_str::SmolStr;
use types::{AssemblerError, AssemblerResult};

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
}

impl Environment {
  /// The default starting address of where instructions get encoded.
  pub const INSTRUCTION_STARTING_ADDRESS: u16 = 0x0000;

  /// The amount of memory available, which is 2^16.
  pub const MEMORY_SIZE: usize = u16::MAX as usize + 1;

  pub fn new() -> Self {
    Self::default()
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

    // Compare the nibbles accordingly depending on the operation we did
    if is_addition {
      self.set_flag(Flags::AuxiliaryCarry, old_nibble + new_nibble > 0x0F);
      // If we added, then we should have a carry if the new value is smaller
      self.set_flag(Flags::Carry, new_value < old_value);
    } else {
      self.set_flag(Flags::AuxiliaryCarry, old_nibble < new_nibble);
      // If we subtracted, then we should have a carry if the new value is greater
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

  /// Writes an address onto the stack, in little endian order.
  pub fn write_stack_address(&mut self, address: u16) {
    // 8085 stores stuff in little endian, so the high byte should be stored first on the stack
    self.write_stack_u8((address >> 8) as u8);
    self.write_stack_u8((address & 0xFF) as u8);
  }

  /// Writes the provided byte onto the stack.
  pub fn write_stack_u8(&mut self, value: u8) {
    self.registers.sp = self.registers.sp.wrapping_sub(1);

    self.write_memory(self.registers.sp, value);
  }

  /// Writes the value to the address.
  pub fn write_memory(&mut self, address: u16, value: u8) {
    *self.memory.get_mut(address as usize).unwrap() = value;
  }

  /// Reads an address from the stack.
  pub fn read_stack_address(&mut self) -> u16 {
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

  /// Reads the byte of memory located at the address.
  pub fn memory_at(&self, address: u16) -> u8 {
    self.memory.get(address as usize).copied().unwrap()
  }

  /// Reads a u16 from memory in little endian, wrapping the program counter if necessary.
  pub fn read_memory_u16(&mut self) -> u16 {
    let lower = self.read_memory();
    let upper = self.read_memory();

    (upper as u16) << 8 | lower as u16
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

  /// Assembles the following instruction into the specified memory address.
  pub fn assemble_instruction(&mut self, address: u16, instruction: u8) {
    *self.memory.get_mut(address as usize).unwrap() = instruction;
  }

  /// Assembles the 16-bit data into memory, in little endian order.
  pub fn assemble_u16(&mut self, address: u16, data: u16) {
    // Intel 8085 uses little endian, so store the low byte first
    self.assemble_instruction(address, (data & 0xFF) as u8);
    self.assemble_instruction(address + 1, (data >> 8) as u8);
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

  /// Encodes the [`InstructionNode`] into the specified spot in memory.
  ///
  /// If it was unable to be encoded, due to the label's address not known at
  /// the time, there will need to be a second pass at encoding.
  pub fn encode_instruction<'a>(
    &mut self,
    assemble_index: u16,
    instruction_node: &'a InstructionNode,
    unassembled: &mut Vec<(&'a InstructionNode, u16)>,
  ) -> AssemblerResult<()> {
    use Instruction::*;

    let addr = Self::INSTRUCTION_STARTING_ADDRESS + assemble_index;

    match (instruction_node.instruction(), instruction_node.operands()) {
      // No operands
      (NOP, &[]) => self.assemble_instruction(addr, encodings::NOP),
      (RAL, &[]) => self.assemble_instruction(addr, encodings::RAL),
      (RLC, &[]) => self.assemble_instruction(addr, encodings::RLC),
      (RRC, &[]) => self.assemble_instruction(addr, encodings::RRC),
      (RAR, &[]) => self.assemble_instruction(addr, encodings::RAR),
      (CMA, &[]) => self.assemble_instruction(addr, encodings::CMA),
      (CMC, &[]) => self.assemble_instruction(addr, encodings::CMC),
      (HLT, &[]) => self.assemble_instruction(addr, encodings::HLT),
      (RNZ, &[]) => self.assemble_instruction(addr, encodings::RNZ),
      (RNC, &[]) => self.assemble_instruction(addr, encodings::RNC),
      (RPO, &[]) => self.assemble_instruction(addr, encodings::RPO),
      (RP, &[]) => self.assemble_instruction(addr, encodings::RP),
      (RZ, &[]) => self.assemble_instruction(addr, encodings::RZ),
      (RC, &[]) => self.assemble_instruction(addr, encodings::RC),
      (RPE, &[]) => self.assemble_instruction(addr, encodings::RPE),
      (RM, &[]) => self.assemble_instruction(addr, encodings::RM),
      (RET, &[]) => self.assemble_instruction(addr, encodings::RET),
      (SPHL, &[]) => self.assemble_instruction(addr, encodings::SPHL),
      (PCHL, &[]) => self.assemble_instruction(addr, encodings::PCHL),
      (XCHG, &[]) => self.assemble_instruction(addr, encodings::XCHG),
      (XTHL, &[]) => self.assemble_instruction(addr, encodings::XTHL),
      (STC, &[]) => self.assemble_instruction(addr, encodings::STC),
      (DAA, &[]) => self.assemble_instruction(addr, encodings::DAA),

      // 1 operand
      (ACI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::ACI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (ACI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::ACI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (SBI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::SBI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (SBI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::SBI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (XRI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::XRI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (XRI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::XRI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (CPI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::CPI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (CPI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::CPI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (ADI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::ADI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (ADI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::ADI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (SUI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::SUI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (SUI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::SUI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (ANI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::ANI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (ANI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::ANI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (ORI, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::ORI);
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (ORI, &[OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encodings::ORI);
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (ADD, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_add(r1)),
      (ADC, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_adc(r1)),
      (SUB, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_sub(r1)),
      (SBB, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_sbb(r1)),
      (ANA, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_ana(r1)),
      (XRA, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_xra(r1)),
      (ORA, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_ora(r1)),
      (CMP, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_cmp(r1)),
      (INX, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_inx(r1)),
      (INR, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_inr(r1)),
      (DCR, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_dcr(r1)),
      (DAD, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_dad(r1)),
      (DCX, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_dcx(r1)),
      (POP, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_pop(r1)),
      (PUSH, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_push(r1)),

      (STA, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::STA);
        self.assemble_u16(addr + 1, data);
      }
      (SHLD, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::SHLD);
        self.assemble_u16(addr + 1, data);
      }
      (STAX, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_stax(r1)),
      (LDA, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::LDA);
        self.assemble_u16(addr + 1, data);
      }
      (LDAX, &[OperandNode::Register(r1)]) => self.assemble_instruction(addr, encode_ldax(r1)),
      (LHLD, &[OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encodings::LHLD);
        self.assemble_u16(addr + 1, data);
      }
      (RST, &[OperandNode::Numeric(num)]) => self.assemble_instruction(addr, encode_rst(num as u8)),
      (JNZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JNZ);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JNC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JNC);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JPO, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JPO);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JP, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JP);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JMP, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JMP);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JZ);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JC);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JPE, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JPE);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JM, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::JM);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CNZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CNZ);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CNC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CNC);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CPO, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CPO);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CP, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CP);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CZ);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CC);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CPE, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CPE);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CM, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CM);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CALL, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction(addr, encodings::CALL);
          self.assemble_u16(addr + 1, jmp_to);
        }
        None => unassembled.push((instruction_node, addr)),
      },

      // 2 Operands
      (LXI, &[OperandNode::Register(r1), OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encode_lxi(r1));
        self.assemble_u16(addr + 1, data);
      }
      (LXI, &[OperandNode::Register(r1), OperandNode::Identifier(ref label)]) => {
        if let Some(label_addr) = self.get_label_address(label) {
          self.assemble_instruction(addr, encode_lxi(r1));
          self.assemble_u16(addr + 1, label_addr);
        } else {
          return Err(AssemblerError::IdentifierNotDefined);
        }
      }
      (LXI, &[OperandNode::Register(r1), OperandNode::String(ref str)]) => {
        if str.len() == 2 {
          let bytes = str.as_bytes();
          let data = (bytes[0] as u16) << 8 | bytes[1] as u16;

          self.assemble_instruction(addr, encode_lxi(r1));
          self.assemble_u16(addr + 1, data);
        } else {
          return Err(AssemblerError::ExpectedTwoByteData);
        }
      }
      (LXI, &[OperandNode::Register(r1), OperandNode::Expression(ref expr)]) => {
        let res = evaluate_expression(self, expr)? as u16;

        self.assemble_instruction(addr, encode_lxi(r1));
        self.assemble_u16(addr + 1, res);
      }

      (MVI, &[OperandNode::Register(r1), OperandNode::Numeric(data)]) => {
        self.assemble_instruction(addr, encode_mvi(r1));
        self.assemble_instruction(addr + 1, (data & 0xFF) as u8);
      }
      (MVI, &[OperandNode::Register(r1), OperandNode::String(ref data)]) => {
        self.assemble_instruction(addr, encode_mvi(r1));
        self.assemble_instruction(addr + 1, data.as_bytes().first().copied().unwrap());
      }
      (MOV, &[OperandNode::Register(r1), OperandNode::Register(r2)]) => {
        self.assemble_instruction(addr, encode_mov(r1, r2));
      }

      (instruction, _) => panic!("missing case when assembling {instruction}"),
    }

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
    }
  }
}

fn evaluate_expression(env: &Environment, expr: &ExpressionNode) -> AssemblerResult<i32> {
  match expr {
    ExpressionNode::Number(num) => Ok(*num),
    ExpressionNode::String(str) => {
      // TODO: Can we evaluate strings that are more than 2 bytes?
      if str.len() > 2 {
        Err(AssemblerError::ExpectedTwoByteData)
      } else {
        let bytes = str.as_bytes();
        let b1 = bytes.first().copied().unwrap_or(0);
        let b2 = bytes.get(1).copied().unwrap_or(0);

        Ok(((b1 as i32) << 8) | b2 as i32)
      }
    }
    ExpressionNode::Identifier(ref label) => match env.get_label_address(label) {
      Some(addr) => Ok(addr as i32),
      None => Err(AssemblerError::IdentifierNotDefined),
    },
    ExpressionNode::Paren(child_expr) => evaluate_expression(env, child_expr),
    ExpressionNode::Unary {
      op,
      expr: child_expr,
    } => match op {
      Operator::Addition => evaluate_expression(env, child_expr),
      Operator::Subtraction => Ok(-evaluate_expression(env, child_expr)?),
      Operator::High => Ok((evaluate_expression(env, child_expr)? >> 8) & 0xFF),
      Operator::Low => Ok(evaluate_expression(env, child_expr)? & 0xFF),
      Operator::Not => Ok(!evaluate_expression(env, child_expr)?),
      _ => unreachable!(),
    },
    ExpressionNode::Binary { op, left, right } => match op {
      Operator::Addition => Ok(evaluate_expression(env, left)? + evaluate_expression(env, right)?),
      Operator::Subtraction => {
        Ok(evaluate_expression(env, left)? - evaluate_expression(env, right)?)
      }
      Operator::Division => Ok(evaluate_expression(env, left)? / evaluate_expression(env, right)?),
      Operator::Multiplication => {
        Ok(evaluate_expression(env, left)? * evaluate_expression(env, right)?)
      }

      Operator::Modulo => Ok(evaluate_expression(env, left)? % evaluate_expression(env, right)?),
      Operator::ShiftLeft => {
        Ok(evaluate_expression(env, left)? << evaluate_expression(env, right)?)
      }
      Operator::ShiftRight => {
        Ok(evaluate_expression(env, left)? >> evaluate_expression(env, right)?)
      }
      Operator::And => Ok(evaluate_expression(env, left)? & evaluate_expression(env, right)?),
      Operator::Or => Ok(evaluate_expression(env, left)? | evaluate_expression(env, right)?),
      Operator::Xor => Ok(evaluate_expression(env, left)? ^ evaluate_expression(env, right)?),

      Operator::Eq => {
        Ok((evaluate_expression(env, left)? == evaluate_expression(env, right)?) as i32)
      }
      Operator::Ne => {
        Ok((evaluate_expression(env, left)? != evaluate_expression(env, right)?) as i32)
      }
      // NOTE: Relational comparisons compare the bits, not the values
      Operator::Lt => Ok(
        ((evaluate_expression(env, left)? as u32) < evaluate_expression(env, right)? as u32) as i32,
      ),
      Operator::Le => Ok(
        ((evaluate_expression(env, left)? as u32) <= evaluate_expression(env, right)? as u32)
          as i32,
      ),
      Operator::Gt => Ok(
        ((evaluate_expression(env, left)? as u32) > evaluate_expression(env, right)? as u32) as i32,
      ),
      Operator::Ge => Ok(
        ((evaluate_expression(env, left)? as u32) >= evaluate_expression(env, right)? as u32)
          as i32,
      ),
      // `NOT`, `HIGH`, `LOW `are handled in the unary section
      Operator::Not | Operator::High | Operator::Low => unreachable!(),
    },
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
