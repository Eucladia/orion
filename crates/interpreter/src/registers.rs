pub use lexer::Register;

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

/// A register pair.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RegisterPair {
  BC,
  DE,
  HL,
  SP,
  PSW,
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

/// Decodes a register from a byte.
///
/// This function will panic if the value is greater than 0x7
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
    _ => panic!("called decode_register with an invalid value"),
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
