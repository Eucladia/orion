mod environment;
mod instructions;
mod interpreter;
mod registers;

pub use environment::Environment;
pub use interpreter::Interpreter;

use lexer::instruction::Instruction;

/// Returns the number of bytes this isntruction occupies in memory
pub fn instruction_bytes_occupied(ins: &Instruction) -> u8 {
  match ins {
    // 0 operand instructions
    Instruction::NOP => 1,
    Instruction::RAL => 1,
    Instruction::RLC => 1,
    Instruction::RRC => 1,
    Instruction::RAR => 1,
    Instruction::CMA => 1,
    Instruction::CMC => 1,
    Instruction::HLT => 1,
    Instruction::RNZ => 1,
    Instruction::RNC => 1,
    Instruction::RPO => 1,
    Instruction::RP => 1,
    Instruction::RZ => 1,
    Instruction::RC => 1,
    Instruction::RPE => 1,
    Instruction::RM => 1,
    Instruction::RET => 1,
    Instruction::XCHG => 1,
    Instruction::XTHL => 1,
    Instruction::SPHL => 1,
    Instruction::PCHL => 1,
    Instruction::STC => 1,
    Instruction::DAA => 1,
    // 1 operand instructions
    Instruction::ACI => 2,
    Instruction::SBI => 2,
    Instruction::XRI => 2,
    Instruction::CPI => 2,
    Instruction::ADD => 1,
    Instruction::ADI => 2,
    Instruction::SUI => 2,
    Instruction::ANI => 2,
    Instruction::ORI => 2,
    Instruction::ADC => 1,
    Instruction::SUB => 1,
    Instruction::SBB => 1,
    Instruction::ANA => 1,
    Instruction::XRA => 1,
    Instruction::ORA => 1,
    Instruction::CMP => 1,
    Instruction::INX => 1,
    Instruction::INR => 1,
    Instruction::DCR => 1,
    Instruction::DAD => 1,
    Instruction::DCX => 1,
    Instruction::POP => 1,
    Instruction::PUSH => 1,
    Instruction::STA => 3,
    Instruction::SHLD => 3,
    Instruction::STAX => 1,
    Instruction::LDA => 3,
    Instruction::LDAX => 1,
    Instruction::LHLD => 3,
    Instruction::JNZ => 3,
    Instruction::JNC => 3,
    Instruction::JPO => 3,
    Instruction::JP => 3,
    Instruction::JMP => 3,
    Instruction::JZ => 3,
    Instruction::JC => 3,
    Instruction::JPE => 3,
    Instruction::JM => 3,
    Instruction::CNZ => 3,
    Instruction::CNC => 3,
    Instruction::CPO => 3,
    Instruction::CP => 3,
    Instruction::CZ => 3,
    Instruction::CC => 3,
    Instruction::CPE => 3,
    Instruction::CM => 3,
    Instruction::CALL => 3,
    Instruction::RST => 1,
    // 2 operand instructions
    Instruction::LXI => 3,
    Instruction::MVI => 2,
    Instruction::MOV => 1,
  }
}
