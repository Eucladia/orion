mod flags;
pub mod instruction;
mod lexer;
mod register;
pub mod token;

pub use flags::Flags;
pub use lexer::Lexer;
pub use register::Register;
pub use token::*;

use types::LexResult;

/// Lexes the input source into a group of tokens.
pub fn lex(src: &str) -> LexResult<Vec<Token>> {
  Lexer::from_string(src).into_iter().collect()
}
