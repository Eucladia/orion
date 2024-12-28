use crate::registers::Registers;
use lexer::{instruction::Instruction, Flags, Register};
use parser::nodes::{InstructionNode, OperandNode};
use smol_str::SmolStr;

use std::collections::HashMap;
use std::ops::Range;

#[derive(Debug)]
pub struct Environment {
  pub flags: u8,
  pub registers: Registers,
  // Label -> address &&  index -> label
  pub label_indices: HashMap<u16, SmolStr>,
  pub labels: HashMap<SmolStr, u16>,
  pub memory: Box<[u8; Environment::MEMORY_SIZE as usize]>,
  // Stores the previous addresses to go to.
  call_stack: Vec<u16>,
}

impl Environment {
  pub const INSTRUCTION_STARTING_ADDRESS: u16 = 0x0000;
  pub const MEMORY_SIZE: u16 = u16::MAX;

  pub fn new() -> Self {
    Self {
      flags: Flags::NONE,
      registers: Registers::default(),
      label_indices: HashMap::new(),
      labels: HashMap::new(),
      memory: Box::new([0; Self::MEMORY_SIZE as usize]),
      call_stack: Vec::new(),
    }
  }

  pub fn is_flag_set(&self, f: Flags) -> bool {
    (self.flags & f as u8) == f as u8
  }

  pub fn set_flag(&mut self, flag: Flags, cond: bool) {
    if cond {
      self.flags |= flag as u8;
    } else {
      self.flags &= !(flag as u8);
    }
  }

  pub fn add_to_call_stack(&mut self, previous_address: u16) {
    self.call_stack.push(previous_address);

    self.registers.sp -= 1;
  }

  pub fn return_from_call(&mut self) -> Option<u16> {
    let e = self.call_stack.pop();

    self.registers.sp += 1;

    e
  }

  /// Encodes an [InstructionNode] into the specified `address` in memory, or the current internal address.
  pub fn encode_instruction<'a>(
    &mut self,
    assemble_index: u16,
    instruction_node: &'a InstructionNode,
    unassembled: &mut Vec<(&'a InstructionNode, u16)>,
  ) {
    use Instruction::*;

    let addr = Self::INSTRUCTION_STARTING_ADDRESS + assemble_index;

    match (instruction_node.instruction(), instruction_node.operands()) {
      // No operands
      (NOP, &[]) => self.assemble_instruction_unchecked(addr, 0x0),
      (RAL, &[]) => self.assemble_instruction_unchecked(addr, 0x17),
      (RLC, &[]) => self.assemble_instruction_unchecked(addr, 0x07),
      (RRC, &[]) => self.assemble_instruction_unchecked(addr, 0x0F),
      (RAR, &[]) => self.assemble_instruction_unchecked(addr, 0x1F),
      (CMA, &[]) => self.assemble_instruction_unchecked(addr, 0x2F),
      (CMC, &[]) => self.assemble_instruction_unchecked(addr, 0x3F),
      (HLT, &[]) => self.assemble_instruction_unchecked(addr, 0x76),
      (RNZ, &[]) => self.assemble_instruction_unchecked(addr, 0xC0),
      (RNC, &[]) => self.assemble_instruction_unchecked(addr, 0xD0),
      (RPO, &[]) => self.assemble_instruction_unchecked(addr, 0xE0),
      (RP, &[]) => self.assemble_instruction_unchecked(addr, 0xF0),
      (RZ, &[]) => self.assemble_instruction_unchecked(addr, 0xC8),
      (RC, &[]) => self.assemble_instruction_unchecked(addr, 0xD8),
      (RPE, &[]) => self.assemble_instruction_unchecked(addr, 0xE8),
      (RM, &[]) => self.assemble_instruction_unchecked(addr, 0xF8),
      (RET, &[]) => self.assemble_instruction_unchecked(addr, 0xC9),

      // 1 operand
      (ACI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xCE);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }
      (SBI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xDE);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }
      (XRI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xEE);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }
      (CPI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xFE);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }
      (ADD, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0x80 + encode_register(r1))
      }
      (ADI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xC6);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }
      (SUI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xD6);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }
      (ANI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xE6);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }
      (ORI, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0xF6);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
      }

      (ADC, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0x88 + encode_register(r1))
      }
      (SUB, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0x90 + encode_register(r1))
      }
      (SBB, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0x98 + encode_register(r1))
      }
      (ANA, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0xA0 + encode_register(r1))
      }
      (XRA, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0xA8 + encode_register(r1))
      }
      (ORA, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0xB0 + encode_register(r1))
      }
      (CMP, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, 0xB8 + encode_register(r1))
      }
      (INX, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_inx(r1))
      }
      (INR, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_inr(r1))
      }
      (DCR, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_dcr(r1))
      }
      (DAD, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_dad(r1))
      }
      (DCX, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_dcx(r1))
      }
      (POP, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_pop(r1))
      }
      (PUSH, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_push(r1))
      }
      (STA, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0x32);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
        self.assemble_instruction_unchecked(addr + 2, (data >> 8) as u8);
      }
      (SHLD, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0x22);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
        self.assemble_instruction_unchecked(addr + 2, (data >> 8) as u8);
      }
      (STAX, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_stax(r1))
      }

      (LDA, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0x3A);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
        self.assemble_instruction_unchecked(addr + 2, (data >> 8) as u8);
      }
      (LDAX, &[OperandNode::Register(r1)]) => {
        self.assemble_instruction_unchecked(addr, encode_ldax(r1))
      }
      (LHLD, &[OperandNode::Literal(data)]) => {
        self.assemble_instruction_unchecked(addr, 0x2A);
        self.assemble_instruction_unchecked(addr + 1, (data & 0xFF) as u8);
        self.assemble_instruction_unchecked(addr + 2, (data >> 8) as u8);
      }
      (JNZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xC2);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JNC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xD2);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JPO, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xE2);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JP, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xF2);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JMP, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xC3);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },

      (JZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xCA);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xDA);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JPE, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xEA);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (JM, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xFA);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },

      (CNZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xC4);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CNC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xD4);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CPO, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xE4);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CP, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xF4);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },

      (CZ, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xCC);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CC, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xDC);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CPE, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xEC);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },
      (CM, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xFC);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },

      (CALL, &[OperandNode::Identifier(ref label)]) => match self.get_label_address(label) {
        Some(jmp_to) => {
          self.assemble_instruction_unchecked(addr, 0xCD);
          self.assemble_instruction_unchecked(addr + 1, (jmp_to & 0xFF) as u8);
          self.assemble_instruction_unchecked(addr + 2, (jmp_to >> 8) as u8);
        }
        None => unassembled.push((instruction_node, addr)),
      },

      // 2 Operands
      (LXI, &[OperandNode::Register(r1), OperandNode::Literal(data)]) => {
        let data = encode_lxi(r1, data);

        self.assemble_instruction_unchecked(addr, data.0);
        self.assemble_instruction_unchecked(addr + 1, data.2);
        self.assemble_instruction_unchecked(addr + 2, data.1);
      }
      (MVI, &[OperandNode::Register(r1), OperandNode::Literal(data)]) => {
        let data = encode_mvi(r1, data);

        // Encode the instruction, then the data
        self.assemble_instruction_unchecked(addr, data.0);
        self.assemble_instruction_unchecked(addr + 1, data.1);
      }
      (MOV, &[OperandNode::Register(r1), OperandNode::Register(r2)]) => {
        self.assemble_instruction_unchecked(addr, encode_mov(r1, r2));
      }
      _ => panic!(),
    }
  }

  pub fn memory_slice_at(&self, range: Range<u16>) -> Option<&[u8]> {
    self.memory.get(range.start as usize..range.end as usize)
  }

  pub fn memory_at(&self, address: u16) -> Option<u8> {
    self.memory.get(address as usize).copied()
  }

  pub fn set_memory_at(&mut self, address: u16, value: u8) {
    *self.memory.get_mut(address as usize).unwrap() = value;
  }

  /// Gets the start of a label from its name
  pub fn get_label_address(&self, label_name: &SmolStr) -> Option<u16> {
    self.labels.get(label_name).copied()
  }

  pub fn add_label(&mut self, label: SmolStr, addr: u16) {
    self.labels.insert(label, addr);
  }

  /// Sets the memory to the specified value.
  ///
  /// Returns [None] if the address was out of bounds.
  pub fn assemble_instruction(&mut self, addr: u16, value: u8) -> Option<()> {
    *self.memory.get_mut(addr as usize)? = value;

    Some(())
  }

  /// Assmebles the value into memory at the specified address.
  ///
  /// SAFETY: The caller needs to make sure that addr is within [u16::MAX].
  pub fn assemble_instruction_unchecked(&mut self, addr: u16, value: u8) {
    // SAFETY: We can verify that the instruction addreses are correct at compile time.
    unsafe {
      *self.memory.get_unchecked_mut(addr as usize) = value;
    }
  }

  /// Completely resets the flags, registers, and memory.
  pub fn reset(&mut self) {
    self.flags = Flags::NONE;
    self.registers = Registers::default();
    // Reuse the underlying allocation
    self.labels.clear();
    self.label_indices.clear();
    self.memory.fill(0);
  }

  /// Resets everything, but leaves the encoded instructions intact
  pub fn reset_runtime(&mut self, assemble_index: u16) {
    self.flags = Flags::NONE;
    self.registers = Registers::default();
    // Reuse the underlying allocation
    self.labels.clear();
    self.label_indices.clear();
    self.memory[assemble_index as usize..].fill(0);
  }
}

// TODO: Remove these panics and handle it in the parser
const fn encode_ldax(r1: Register) -> u8 {
  match r1 {
    Register::B => 0x0A,
    Register::D => 0x1A,
    _ => panic!("invalid register passed to encode_ldax"),
  }
}
const fn encode_stax(r1: Register) -> u8 {
  match r1 {
    Register::B => 0x02,
    Register::D => 0x12,
    _ => panic!("invalid register passed to encode_stax"),
  }
}

const fn encode_push(r1: Register) -> u8 {
  match r1 {
    Register::B => 0xC5,
    Register::D => 0xD5,
    Register::H => 0xE5,
    _ => panic!("invalid register passed to encode_push"),
  }
}

const fn encode_pop(r1: Register) -> u8 {
  match r1 {
    Register::B => 0xC1,
    Register::D => 0xD1,
    Register::H => 0xE1,
    _ => panic!("invalid register passed to encode_pop"),
  }
}

const fn encode_dcx(r1: Register) -> u8 {
  match r1 {
    Register::B => 0x0B,
    Register::D => 0x1B,
    Register::H => 0x2B,
    _ => panic!("invalid register passed to encode_dcx"),
  }
}

const fn encode_dad(r1: Register) -> u8 {
  match r1 {
    Register::B => 0x09,
    Register::D => 0x19,
    Register::H => 0x29,
    _ => panic!("invalid register passed to encode_dad"),
  }
}

const fn encode_inx(r1: Register) -> u8 {
  match r1 {
    Register::B => 0x03,
    Register::D => 0x13,
    Register::H => 0x23,
    _ => panic!("invalid register passed to encode_inx"),
  }
}

const fn encode_lxi(r1: Register, data: u16) -> (u8, u8, u8) {
  let reg = match r1 {
    Register::B => 0x01,
    Register::D => 0x11,
    Register::H => 0x21,
    _ => panic!("invalid register passed to lxi instruction"),
  };

  let lower_half = data & 0xFF;
  let upper_half = data >> 8;

  (reg, upper_half as u8, lower_half as u8)
}

const fn encode_mvi(r1: Register, data: u16) -> (u8, u8) {
  let reg = match r1 {
    Register::B => 0x06,
    Register::D => 0x16,
    Register::H => 0x26,
    Register::M => 0x36,
    // 8 bit registers
    Register::C => 0xE,
    Register::E => 0x1E,
    Register::L => 0x2E,
    Register::A => 0x3E,
    _ => unreachable!(),
  };

  (reg, (data & 0xFF) as u8)
}

const fn encode_dcr(r1: Register) -> u8 {
  match r1 {
    Register::B => 0x05,
    Register::D => 0x15,
    Register::H => 0x25,
    Register::M => 0x35,
    // 8 bit registers
    Register::C => 0x0D,
    Register::E => 0x1D,
    Register::L => 0x2D,
    Register::A => 0x3D,
    _ => unreachable!(),
  }
}
const fn encode_inr(r1: Register) -> u8 {
  match r1 {
    Register::B => 0x04,
    Register::D => 0x14,
    Register::H => 0x24,
    Register::M => 0x34,
    // 8 bit registers
    Register::C => 0x0C,
    Register::E => 0x1C,
    Register::L => 0x2C,
    Register::A => 0x3C,
    _ => unreachable!(),
  }
}
const fn encode_mov(r1: Register, r2: Register) -> u8 {
  // The normal value for `MOV M, A`, 0x76, actually corresponds to `HLT`
  if matches!((r1, r2), (Register::M, Register::A)) {
    return 0x77;
  }

  let base = 0x40;

  base + (encode_register(r1) * 8) + encode_register(r2)
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
