use crate::Environment;
use lexer::Register;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registers {
  /// Register `A`
  pub a: u8,
  /// Register `B`
  pub b: u8,
  /// Register `C`
  pub c: u8,
  /// Register `D`
  pub d: u8,
  /// Register `E`
  pub e: u8,
  /// Register `H`
  pub h: u8,
  /// Register `L`
  pub l: u8,

  /// Program counter.
  pub pc: u16,
  /// Stack pointer.
  pub sp: u16,

  /// Instruction register.
  pub ir: u8,
}

impl Registers {
  pub fn new() -> Self {
    Self::default()
  }

  /// Updates the program counter, wrapping around if necessary, and returns it.
  pub fn next_pc(&mut self) -> u16 {
    self.pc = self.pc.wrapping_add(1);

    self.pc
  }
}

/// Sets the value of the register.
///
/// If the register is [`Register::M`], then the value at the memory address
/// of register pair H-L will be set.
pub fn set_register_value(env: &mut Environment, dest_reg: Register, value: u8) {
  match dest_reg {
    Register::A => env.registers.a = value,
    Register::B => env.registers.b = value,
    Register::C => env.registers.c = value,
    Register::D => env.registers.d = value,
    Register::E => env.registers.e = value,
    Register::H => env.registers.h = value,
    Register::L => env.registers.l = value,

    Register::M => env.write_memory(
      env.memory_at((env.registers.h as u16) << 8 | env.registers.l as u16) as u16,
      value,
    ),
    _ => unreachable!(),
  }
}

/// Reads the value of the register.
///
/// If the register is [`Register::M`], then the value at the memory address
/// of register pair H-L is returned.
pub fn get_register_value(env: &Environment, reg: Register) -> Option<u8> {
  Some(match reg {
    Register::A => env.registers.a,
    Register::B => env.registers.b,
    Register::C => env.registers.c,
    Register::D => env.registers.d,
    Register::E => env.registers.e,
    Register::H => env.registers.h,
    Register::L => env.registers.l,
    Register::M => env.memory_at((env.registers.h as u16) << 8 | env.registers.l as u16),
    _ => unreachable!(),
  })
}

pub const fn decode_register(byte: u8) -> Register {
  match byte {
    0 => Register::B,
    1 => Register::C,
    2 => Register::D,
    3 => Register::E,
    4 => Register::H,
    5 => Register::L,
    6 => Register::M,
    7 => Register::A,
    _ => panic!("got invalid byte register"),
  }
}

impl Default for Registers {
  fn default() -> Self {
    Self {
      // General purpose registers
      a: 0,
      b: 0,
      c: 0,
      d: 0,
      e: 0,
      h: 0,
      l: 0,

      // Program counter
      pc: 0,
      // Stack pointer
      sp: u16::MAX,
      // Instruction register
      ir: 0,
    }
  }
}
