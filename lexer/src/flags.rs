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
