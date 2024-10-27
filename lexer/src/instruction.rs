#[allow(clippy::upper_case_acronyms)]
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Instruction {
  // Data movement
  MOV,
  MVI,
  LDA,
  LDAX,
  LHLD,
  STA,
  STAX,
  SHLD,
  LXI,
  PUSH,
  POP,
  // Arithmetical and Logical
  ADD,
  ADC,
  ADI,
  ACI,
  SUB,
  SBB,
  SUI,
  SBI,
  INR,
  DCR,
  INX,
  DCX,
  DAD,
  CMA,
  CMC,
  CMP,
  CPI,
  RAL,
  RAR,
  RLC,
  RRC,
  ANA,
  ANI,
  ORA,
  ORI,
  XRA,
  XRI,
  // Program flow
  JMP,
  JZ,
  JNZ,
  JC,
  JNC,
  JP,
  JM,
  JPE,
  JPO,
  CALL,
  CZ,
  CNZ,
  CC,
  CNC,
  CP,
  CM,
  CPE,
  CPO,
  RET,
  RZ,
  RNZ,
  RC,
  RNC,
  RP,
  RM,
  RPE,
  RPO,
  // Processor control
  HLT,
  // No op
  NOP,
}

impl Instruction {
  /// Whether the given string is an instruction.
  pub fn is_opcode(string: &str) -> bool {
    Self::from_string(string).is_some()
  }

  /// The number of operands that this instruction has.
  pub const fn num_operands(self) -> usize {
    use Instruction::*;

    match self {
      MOV | MVI | LXI => 2,

      LDA | LDAX | LHLD | STA | STAX | SHLD | PUSH | POP | ADD | ADC | ADI | ACI | SUB | SBB
      | SUI | SBI | INR | DCR | INX | DCX | DAD | CMP | CPI | ANA | ANI | ORA | ORI | XRA | XRI
      | JMP | JZ | JNZ | JC | JNC | JP | JM | JPE | JPO | CALL | CZ | CNZ | CC | CNC | CP | CM
      | CPE | CPO => 1,

      CMA | CMC | RAL | RAR | RLC | RRC | RET | RZ | RNZ | RC | RNC | RP | RM | RPE | RPO | HLT
      | NOP => 0,
    }
  }

  /// Parses an [Instruction] from a string.
  pub fn from_string(string: &str) -> Option<Self> {
    match string {
      string if string.eq_ignore_ascii_case("mov") => Some(Instruction::MOV),
      string if string.eq_ignore_ascii_case("mvi") => Some(Instruction::MVI),
      string if string.eq_ignore_ascii_case("lda") => Some(Instruction::LDA),
      string if string.eq_ignore_ascii_case("sta") => Some(Instruction::STA),
      string if string.eq_ignore_ascii_case("stax") => Some(Instruction::STAX),
      string if string.eq_ignore_ascii_case("lxi") => Some(Instruction::LXI),
      string if string.eq_ignore_ascii_case("push") => Some(Instruction::PUSH),
      string if string.eq_ignore_ascii_case("pop") => Some(Instruction::POP),
      string if string.eq_ignore_ascii_case("add") => Some(Instruction::ADD),
      string if string.eq_ignore_ascii_case("adc") => Some(Instruction::ADC),
      string if string.eq_ignore_ascii_case("adi") => Some(Instruction::ADI),
      string if string.eq_ignore_ascii_case("aci") => Some(Instruction::ACI),
      string if string.eq_ignore_ascii_case("sub") => Some(Instruction::SUB),
      string if string.eq_ignore_ascii_case("sbb") => Some(Instruction::SBB),
      string if string.eq_ignore_ascii_case("sui") => Some(Instruction::SUI),
      string if string.eq_ignore_ascii_case("sbi") => Some(Instruction::SBI),
      string if string.eq_ignore_ascii_case("inr") => Some(Instruction::INR),
      string if string.eq_ignore_ascii_case("dcr") => Some(Instruction::DCR),
      string if string.eq_ignore_ascii_case("inx") => Some(Instruction::INX),
      string if string.eq_ignore_ascii_case("dcx") => Some(Instruction::DCX),
      string if string.eq_ignore_ascii_case("dad") => Some(Instruction::DAD),
      string if string.eq_ignore_ascii_case("cma") => Some(Instruction::CMA),
      string if string.eq_ignore_ascii_case("cmc") => Some(Instruction::CMC),
      string if string.eq_ignore_ascii_case("cmp") => Some(Instruction::CMP),
      string if string.eq_ignore_ascii_case("cpi") => Some(Instruction::CPI),
      string if string.eq_ignore_ascii_case("ral") => Some(Instruction::RAL),
      string if string.eq_ignore_ascii_case("rar") => Some(Instruction::RAR),
      string if string.eq_ignore_ascii_case("rlc") => Some(Instruction::RLC),
      string if string.eq_ignore_ascii_case("rrc") => Some(Instruction::RRC),
      string if string.eq_ignore_ascii_case("ana") => Some(Instruction::ANA),
      string if string.eq_ignore_ascii_case("ani") => Some(Instruction::ANI),
      string if string.eq_ignore_ascii_case("ora") => Some(Instruction::ORA),
      string if string.eq_ignore_ascii_case("ori") => Some(Instruction::ORI),
      string if string.eq_ignore_ascii_case("xra") => Some(Instruction::XRA),
      string if string.eq_ignore_ascii_case("xri") => Some(Instruction::XRI),
      string if string.eq_ignore_ascii_case("jmp") => Some(Instruction::JMP),
      string if string.eq_ignore_ascii_case("jz") => Some(Instruction::JZ),
      string if string.eq_ignore_ascii_case("jnz") => Some(Instruction::JNZ),
      string if string.eq_ignore_ascii_case("jc") => Some(Instruction::JC),
      string if string.eq_ignore_ascii_case("jnc") => Some(Instruction::JNC),
      string if string.eq_ignore_ascii_case("jp") => Some(Instruction::JP),
      string if string.eq_ignore_ascii_case("jm") => Some(Instruction::JM),
      string if string.eq_ignore_ascii_case("jpe") => Some(Instruction::JPE),
      string if string.eq_ignore_ascii_case("jpo") => Some(Instruction::JPO),
      string if string.eq_ignore_ascii_case("call") => Some(Instruction::CALL),
      string if string.eq_ignore_ascii_case("cz") => Some(Instruction::CZ),
      string if string.eq_ignore_ascii_case("cnz") => Some(Instruction::CNZ),
      string if string.eq_ignore_ascii_case("cc") => Some(Instruction::CC),
      string if string.eq_ignore_ascii_case("cnc") => Some(Instruction::CNC),
      string if string.eq_ignore_ascii_case("cp") => Some(Instruction::CP),
      string if string.eq_ignore_ascii_case("cm") => Some(Instruction::CM),
      string if string.eq_ignore_ascii_case("cpe") => Some(Instruction::CPE),
      string if string.eq_ignore_ascii_case("cpo") => Some(Instruction::CPO),
      string if string.eq_ignore_ascii_case("ret") => Some(Instruction::RET),
      string if string.eq_ignore_ascii_case("rz") => Some(Instruction::RZ),
      string if string.eq_ignore_ascii_case("rnz") => Some(Instruction::RNZ),
      string if string.eq_ignore_ascii_case("rc") => Some(Instruction::RC),
      string if string.eq_ignore_ascii_case("rnc") => Some(Instruction::RNC),
      string if string.eq_ignore_ascii_case("rp") => Some(Instruction::RP),
      string if string.eq_ignore_ascii_case("rm") => Some(Instruction::RM),
      string if string.eq_ignore_ascii_case("rpe") => Some(Instruction::RPE),
      string if string.eq_ignore_ascii_case("rpo") => Some(Instruction::RPO),
      string if string.eq_ignore_ascii_case("hlt") => Some(Instruction::HLT),
      string if string.eq_ignore_ascii_case("nop") => Some(Instruction::NOP),
      _ => None,
    }
  }
}

impl std::fmt::Display for Instruction {
  fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(fmt, "{:?}", self)
  }
}
