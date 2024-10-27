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
  /// Data register that contains operands for the instruction register.
  pub dr: u16,
}

impl Default for Registers {
  fn default() -> Self {
    Self {
      a: 0,
      b: 0,
      c: 0,
      d: 0,
      e: 0,
      h: 0,
      l: 0,

      pc: 0,
      sp: u16::MAX,

      ir: 0,
      dr: 0,
    }
  }
}
