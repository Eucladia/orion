#[repr(u8)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Flags {
  Zero,
  Carry,
  Sign,
  Parity,
  AuxiliaryCarry,
}

impl Flags {
  pub fn is_flag(string: &str) -> bool {
    Self::from_str(string).is_some()
  }

  pub fn from_str(string: &str) -> Option<Self> {
    match string {
      string if string.eq_ignore_ascii_case("zero") => Some(Flags::Zero),
      string if string.eq_ignore_ascii_case("carry") => Some(Flags::Carry),
      string if string.eq_ignore_ascii_case("sign") => Some(Flags::Sign),
      string if string.eq_ignore_ascii_case("parity") => Some(Flags::Parity),
      string if string.eq_ignore_ascii_case("auxiliarycarry") => Some(Flags::AuxiliaryCarry),
      _ => None,
    }
  }
}
