/// Directives to tell the assembler.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Directive {
  /// Defines up to 8 comma-separated 16 bit values, in the form of `name EQU d16`.
  EQU,
  /// Defines up to 8 comma-separated 16 bit values, in the form of `name EQU d16`.
  ///
  /// Unlike the `EQU` directive, `SET` allows redefining the name.
  SET,
  /// Defines up to 8 comma-separated 8 bit values, in the form of `DW d8`.
  DB,
  /// Defines up to 8 comma-separated 16 bit values, in the form of `DW d16`.
  DW,
  /// Reserves the following memory locations, in the form of `DS d16`.
  DS,
  /// Starts assembling at the provided address, in the form of `ORG d16`
  ORG,
  /// Tells the assembler to stop assembling.
  END,
}

impl Directive {
  pub fn is_directive(val: &str) -> bool {
    Self::from_string(val).is_some()
  }

  /// Returns a directive from a string.
  pub fn from_string(val: &str) -> Option<Self> {
    match val {
      "equ" | "eqU" | "eQu" | "eQU" | "Equ" | "EqU" | "EQu" | "EQU" => Some(Directive::EQU),
      "set" | "seT" | "sEt" | "sET" | "Set" | "SeT" | "SEt" | "SET" => Some(Directive::SET),
      "db" | "dB" | "Db" | "DB" => Some(Directive::DB),
      "dw" | "dW" | "Dw" | "DW" => Some(Directive::DW),
      "ds" | "dS" | "Ds" | "DS" => Some(Directive::DS),
      "org" | "orG" | "oRg" | "oRG" | "Org" | "OrG" | "ORg" | "ORG" => Some(Directive::ORG),
      "end" | "enD" | "eNd" | "eND" | "End" | "EnD" | "ENd" | "END" => Some(Directive::END),
      _ => None,
    }
  }
}

impl std::fmt::Display for Directive {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Directive::EQU => write!(f, "EQU"),
      Directive::SET => write!(f, "SET"),
      Directive::DB => write!(f, "DB"),
      Directive::DW => write!(f, "DW"),
      Directive::DS => write!(f, "DS"),
      Directive::ORG => write!(f, "ORG"),
      Directive::END => write!(f, "END"),
    }
  }
}
