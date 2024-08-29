#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Register {
  A,
  B,
  C,
  D,
  E,
  H,
  L,
  // Psuedo-register that points to H-L register pair
  M,
}

impl Register {
  pub fn is_matching_pair(self, other: Self) -> bool {
    Self::are_register_pairs(self, other)
  }

  pub fn are_register_pairs(r1: Self, r2: Self) -> bool {
    match (r1, r2) {
      // The order matters, I think
      (Register::B, Register::C) | (Register::D, Register::E) | (Register::H, Register::L) => true,
      _ => false,
    }
  }

  pub fn is_register(string: &str) -> bool {
    Self::from_str(string).is_some()
  }

  pub fn from_str(string: &str) -> Option<Self> {
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
