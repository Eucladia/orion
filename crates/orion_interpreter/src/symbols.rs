use smol_str::SmolStr;
use std::collections::HashMap;

/// The user defined symbols of a program.
#[derive(Debug)]
pub struct Symbols<'a>(HashMap<&'a SmolStr, Symbol>);

/// A user defined symbol via a directive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
  /// The location counter when this symbol was first defined.
  pub defined_at: u16,
  /// The value of this symbol.
  pub value: u16,
}

impl Default for Symbols<'_> {
  fn default() -> Self {
    Self::new()
  }
}

impl<'a> Symbols<'a> {
  pub fn new() -> Self {
    Self(HashMap::new())
  }

  /// Checks if the following [`Symbol`] exists.
  pub fn contains(&self, name: &'a SmolStr) -> bool {
    self.0.contains_key(name)
  }

  /// Adds a new [`Symbol `]with the following value and location counter.
  pub fn add_symbol(&mut self, name: &'a SmolStr, value: u16, defined_at: u16) {
    self.0.insert(name, Symbol { defined_at, value });
  }

  /// Updates the [`Symbol`], returning true if the symbol existed and was updated.
  pub fn insert_or_update(&mut self, name: &'a SmolStr, value: u16, new_location: u16) -> bool {
    if let Some(symbol) = self.0.get_mut(name) {
      symbol.value = value;
      true
    } else {
      self.0.insert(
        name,
        Symbol {
          defined_at: new_location,
          value,
        },
      );
      false
    }
  }

  /// Gets the value of the  [`Symbol`].
  pub fn get_value(&self, name: &'a SmolStr) -> Option<u16> {
    self.0.get(name).map(|x| x.value)
  }

  /// Gets the value of the [`Symbol`], if it was defined before the location counter.
  pub fn get_defined_value(&self, name: &'a SmolStr, location: u16) -> Option<u16> {
    self.0.get(name).and_then(|x| {
      if x.defined_at <= location {
        Some(x.value)
      } else {
        None
      }
    })
  }
}
