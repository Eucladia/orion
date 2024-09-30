#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Register {
  /// Register A.
  ///
  /// A special register that acts as an accumulator.
  A,
  /// Register B.
  ///
  /// Register `B` pairs with register `C`.
  B,
  /// Register C.
  C,
  /// Register D.
  ///
  /// Register `D` pairs with register `E`.
  D,
  /// Register E.
  E,
  /// Register H.
  ///
  /// Register `H` pairs with register `L`.
  H,
  /// Register L.
  L,
  /// Pseudo-register M.
  ///
  /// This register points to the H-L register pair.
  M,
}

impl Register {
  /// Whether this [Register] is pair-able with the other one.
  pub fn is_matching_pair(self, other: Self) -> bool {
    Self::are_register_pairs(self, other)
  }

  /// Whether these 2 [Register]s are pairs.
  pub fn are_register_pairs(r1: Self, r2: Self) -> bool {
    match (r1, r2) {
      // The order matters, I think
      (Register::B, Register::C) | (Register::D, Register::E) | (Register::H, Register::L) => true,
      _ => false,
    }
  }

  /// Whether a given string is a register, case insensitive
  pub fn is_register(string: &str) -> bool {
    Self::from_string(string).is_some()
  }

  /// Parse a [Register] from a string.
  pub fn from_string(string: &str) -> Option<Self> {
    match string {
      "a" | "A" => Some(Register::A),
      "b" | "B" => Some(Register::B),
      "c" | "C" => Some(Register::C),
      "d" | "D" => Some(Register::D),
      "e" | "E" => Some(Register::E),
      "h" | "H" => Some(Register::H),
      "l" | "L" => Some(Register::L),
      "m" | "M" => Some(Register::M),
      _ => None,
    }
  }
}

impl std::fmt::Display for Register {
  fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(fmt, "{:?}", self)
  }
}
