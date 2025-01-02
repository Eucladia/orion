pub mod nodes;
pub mod parser;

#[macro_export]
macro_rules! unwrap {
  ($expr:expr) => {{
    #[cfg(debug_assertions)]
    {
      $expr.unwrap()
    }
    #[cfg(not(debug_assertions))]
    unsafe {
      $expr.unwrap_unchecked()
    }
  }};
}
