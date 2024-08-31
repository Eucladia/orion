#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Flags {
  /// Set if the resulting operation produced a `0`.
  Zero = 1 << 0,
  /// Set if the resulting operation produced a carry.
  Carry = 1 << 1,
  /// Set if the resulting operation produced a negative number.
  Sign = 1 << 2,
  /// Set if the resulting operation produced an even number of `1`s.
  Parity = 1 << 3,
  /// Set if the resulting operation produced a carry over the nibbles.
  AuxiliaryCarry = 1 << 4,
}

impl Flags {
  /// Whether or the given string is a [Flags].
  pub fn is_flag(string: &str) -> bool {
    Self::from_string(string).is_some()
  }

  /// Parses a [Flags] from a string.
  pub fn from_string(string: &str) -> Option<Self> {
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
