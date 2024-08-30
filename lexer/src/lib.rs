mod flags;
mod instruction;
mod lexer;
mod register;
mod token;

/// Creates a [Token] with the following [TokenKind] and length
#[macro_export]
macro_rules! create_token {
  ($token:tt, $len:expr) => {
    $crate::token::Token::new($crate::token::TokenKind::$token, $len)
  };
}

pub use flags::Flags;
pub use lexer::Lexer;
pub use register::Register;
pub use token::*;
