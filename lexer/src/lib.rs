mod flags;
pub mod instruction;
mod lexer;
mod register;
pub mod token;

pub use flags::Flags;
pub use lexer::Lexer;
pub use register::Register;
pub use token::*;

/// Lexes the input source into a group of tokens.
pub fn lex(src: &str) -> types::LexResult<Vec<Token>> {
  Lexer::from_string(src).collect()
}
