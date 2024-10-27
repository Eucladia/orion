mod environment;
mod interpreter;
mod registers;

pub type InterpreterResult<T> = std::result::Result<T, InterpreterError>;
#[derive(Debug, Clone)]
pub enum InterpreterError {}

pub use environment::Environment;
pub use interpreter::Interpreter;
