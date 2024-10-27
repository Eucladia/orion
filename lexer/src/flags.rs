#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
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
  pub const NONE: u8 = 0;
  pub const ALL: u8 = Flags::Zero as u8
    | Flags::Carry as u8
    | Flags::Sign as u8
    | Flags::Parity as u8
    | Flags::AuxiliaryCarry as u8;
}
