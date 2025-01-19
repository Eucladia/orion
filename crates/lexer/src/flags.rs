/// The flags for the Intel 8085 processor.
///
/// The flags are stored in the following order:
///
/// | Bit # | 7   6   5   4   3   2   1   0  |
/// |----------------------------------------|
/// | Flag  | S   Z   0   AC  0   P   0   CY |
///
/// Bits 1, 3, and 5 are "undefined" on 8085, thus set to 0 erroneously.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum Flags {
  /// Set if the resulting operation produced a carry.
  Carry = 1 << 0,
  /// "Overflow" flag, undocumented.
  Overflow = 1 << 1,
  /// Set if the resulting operation produced an even number of `1`s.
  Parity = 1 << 2,
  /// An unused flag that is always set to 0, undocumented.
  Z = 1 << 3,
  /// Set if the resulting operation produced a carry over the nibbles.
  AuxiliaryCarry = 1 << 4,
  /// "K" flag for overflow or underflow, undocumented.
  K = 1 << 5,
  /// Set if the resulting operation produced a `0`.
  Zero = 1 << 6,
  /// Set if the resulting operation produced a negative number.
  Sign = 1 << 7,
}

impl Flags {
  /// A bitset with none of the [`Flags`] set.
  pub const NONE: u8 = 0;

  /// A bitset with all of the [`Flags`] set.
  pub const ALL: u8 = Flags::Zero as u8
    | Flags::Carry as u8
    | Flags::Sign as u8
    | Flags::Parity as u8
    | Flags::AuxiliaryCarry as u8;
}
