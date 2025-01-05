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
  /// Stack Pointer.
  ///
  /// Not a real register but it can be used as one in certain instructions.
  SP,
  /// Program Status Word.
  ///
  /// Not a real register but it can be used as one in certain instructions, to
  /// store the accumulator and flags
  PSW,
}

impl Register {
  /// Whether this [`Register`] is pair-able with the other one.
  pub const fn is_matching_pair(self, other: Self) -> bool {
    Self::are_register_pairs(self, other)
  }

  /// Whether these 2 [`Register`]s are pairs.
  pub const fn are_register_pairs(r1: Self, r2: Self) -> bool {
    matches!(
      (r1, r2),
      (Register::B, Register::C) | (Register::D, Register::E) | (Register::H, Register::L)
    )
  }

  /// Whether a given string is a register, case insensitive
  pub fn is_register(string: &str) -> bool {
    Self::from_string(string).is_some()
  }

  /// Parse a [`Register`] from a string.
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
      "psw" | "psW" | "pSw" | "pSW" | "Psw" | "PsW" | "PSw" | "PSW" => Some(Register::PSW),
      "sp" | "sP" | "Sp" | "SP" => Some(Register::SP),
      _ => None,
    }
  }
}

impl std::fmt::Display for Register {
  fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(fmt, "{:?}", self)
  }
}
