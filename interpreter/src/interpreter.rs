use crate::{encodings, instructions, Environment};
use parser::nodes::{Node, ProgramNode};
use types::{AssembleError, AssembleErrorKind};

#[derive(Debug)]
pub struct Interpreter {
  node: ProgramNode,
  env: Environment,
}

impl Interpreter {
  pub fn new(ast: ProgramNode) -> Self {
    Self {
      node: ast,
      env: Environment::new(),
    }
  }

  /// Assmebles the assembly, encoding the instructions into memory.
  pub fn assemble(&mut self) -> types::AssembleResult<()> {
    let mut unassembled = Vec::new();

    for node in self.node.children() {
      match node {
        Node::Instruction(insn) => {
          self
            .env
            .encode_instruction(self.env.assemble_index, insn, &mut unassembled, false)?;
        }
        Node::Label(label) => {
          let label_name = label.label_name();

          if self.env.labels.contains_key(&label_name) {
            return Err(AssembleError::new(
              label.span().start,
              AssembleErrorKind::LabelRedefined,
            ));
          }

          // The label is to be inserted at the current address will be the address to go to
          let lower = (self.env.assemble_index & 0xFF) as u8;
          let upper = (self.env.assemble_index >> 8) as u8;

          let addr = Environment::INSTRUCTION_STARTING_ADDRESS + self.env.assemble_index;

          self.env.assemble_instruction(addr, lower);
          self.env.assemble_instruction(addr + 1, upper);
          // Make this index (and the next) as a label index
          self.env.label_indices.insert(addr, label_name.clone());

          self.env.assemble_index += 2;

          // Point this label to the instruction's that should be executed
          self.env.add_label(label_name, self.env.assemble_index);
        }
      };
    }

    // Everything should be assembled after this second pass
    let mut new_unassembled = vec![];

    if !unassembled.is_empty() {
      for elem in unassembled.iter() {
        self
          .env
          .encode_instruction(elem.1, elem.0, &mut new_unassembled, true)?;
      }
    }

    for n in 0..30 {
      eprintln!("0x{:X}: 0x{:X}", n, self.env.memory_at(n));
    }

    Ok(())
  }

  /// Resets the interpreter, wiping all memory and registers.
  ///
  /// If `wipe_encoded` is `false`, then the assembled instructions in memory are preserved.
  pub fn reset(&mut self, wipe_encoded: bool) {
    if wipe_encoded {
      self.env.reset(0);
      self.env.assemble_index = 0;
    } else {
      self.env.reset(self.env.assemble_index);
    }
  }

  fn fetch_instruction(&mut self) -> Option<u8> {
    if self.env.registers.pc >= self.env.assemble_index {
      return None;
    }

    Some(self.env.memory_at(self.env.registers.pc))
  }

  /// Execute's the next instruction in memory.
  pub fn execute(&mut self) -> Option<()> {
    let fetched = self.fetch_instruction()?;

    self.execute_instruction(fetched);

    Some(())
  }

  fn execute_instruction(&mut self, byte: u8) {
    if self.env.label_indices.contains_key(&self.env.registers.pc) {
      // Labels are 16 bits
      self.env.registers.pc = self.env.registers.pc.wrapping_add(2);

      return;
    }

    match byte {
      // Register, Register operands
      b if (encodings::MOV_B_B..=encodings::MOV_A_A).contains(&b) && b != encodings::HLT => {
        instructions::execute_mov(&mut self.env, byte)
      }

      // Register, d16 operands
      encodings::LXI_B | encodings::LXI_D | encodings::LXI_H | encodings::LXI_SP => {
        instructions::execute_lxi(&mut self.env, byte)
      }

      // Register, d8 operands
      encodings::MVI_B
      | encodings::MVI_D
      | encodings::MVI_H
      | encodings::MVI_M
      | encodings::MVI_C
      | encodings::MVI_E
      | encodings::MVI_L
      | encodings::MVI_A => instructions::execute_mvi(&mut self.env, byte),

      // Register operands
      encodings::LDAX_B | encodings::LDAX_D => instructions::execute_ldax(&mut self.env, byte),
      encodings::STAX_B | encodings::STAX_D => instructions::execute_stax(&mut self.env, byte),
      encodings::DCX_B | encodings::DCX_D | encodings::DCX_H | encodings::DCX_SP => {
        instructions::execute_dcx(&mut self.env, byte)
      }
      encodings::INX_B | encodings::INX_D | encodings::INX_H | encodings::INX_SP => {
        instructions::execute_inx(&mut self.env, byte)
      }
      encodings::DAD_B | encodings::DAD_D | encodings::DAD_H | encodings::DAD_SP => {
        instructions::execute_dad(&mut self.env, byte)
      }
      encodings::DCR_A
      | encodings::DCR_B
      | encodings::DCR_C
      | encodings::DCR_D
      | encodings::DCR_E
      | encodings::DCR_H
      | encodings::DCR_L
      | encodings::DCR_M => instructions::execute_dcr(&mut self.env, byte),
      encodings::INR_A
      | encodings::INR_B
      | encodings::INR_C
      | encodings::INR_D
      | encodings::INR_E
      | encodings::INR_H
      | encodings::INR_L
      | encodings::INR_M => instructions::execute_inr(&mut self.env, byte),
      encodings::ADD_B..=encodings::ADD_A => instructions::execute_add(&mut self.env, byte),
      encodings::ADC_B..=encodings::ADC_A => instructions::execute_adc(&mut self.env, byte),
      encodings::SUB_B..=encodings::SUB_A => instructions::execute_sub(&mut self.env, byte),
      encodings::SBB_B..=encodings::SBB_A => instructions::execute_sbb(&mut self.env, byte),
      encodings::ORA_B..=encodings::ORA_A => instructions::execute_ora(&mut self.env, byte),
      encodings::XRA_B..=encodings::XRA_A => instructions::execute_xra(&mut self.env, byte),
      encodings::ANA_B..=encodings::ANA_A => instructions::execute_ana(&mut self.env, byte),
      encodings::CMP_B..=encodings::CMP_A => instructions::execute_cmp(&mut self.env, byte),
      encodings::PUSH_B | encodings::PUSH_D | encodings::PUSH_H | encodings::PUSH_PSW => {
        instructions::execute_push(&mut self.env, byte)
      }
      encodings::POP_B | encodings::POP_D | encodings::POP_H | encodings::POP_PSW => {
        instructions::execute_pop(&mut self.env, byte)
      }

      // a16 operands
      encodings::JP => instructions::execute_jp(&mut self.env, byte),
      encodings::CP => instructions::execute_cp(&mut self.env, byte),
      encodings::JC => instructions::execute_jc(&mut self.env, byte),
      encodings::JZ => instructions::execute_jz(&mut self.env, byte),
      encodings::JM => instructions::execute_jm(&mut self.env, byte),
      encodings::CC => instructions::execute_cc(&mut self.env, byte),
      encodings::CZ => instructions::execute_cz(&mut self.env, byte),
      encodings::CM => instructions::execute_cm(&mut self.env, byte),
      encodings::JNZ => instructions::execute_jnz(&mut self.env, byte),
      encodings::JNC => instructions::execute_jnc(&mut self.env, byte),
      encodings::JPO => instructions::execute_jpo(&mut self.env, byte),
      encodings::JMP => instructions::execute_jmp(&mut self.env, byte),
      encodings::JPE => instructions::execute_jpe(&mut self.env, byte),
      encodings::CNC => instructions::execute_cnc(&mut self.env, byte),
      encodings::CNZ => instructions::execute_cnz(&mut self.env, byte),
      encodings::CPO => instructions::execute_cpo(&mut self.env, byte),
      encodings::CPE => instructions::execute_cpe(&mut self.env, byte),
      encodings::CALL => instructions::execute_call(&mut self.env, byte),
      encodings::SHLD => instructions::execute_shld(&mut self.env, byte),
      encodings::LHLD => instructions::execute_lhld(&mut self.env, byte),
      encodings::STA => instructions::execute_sta(&mut self.env, byte),
      encodings::LDA => instructions::execute_lda(&mut self.env, byte),

      // d8 operands
      encodings::ADI => instructions::execute_adi(&mut self.env, byte),
      encodings::ACI => instructions::execute_aci(&mut self.env, byte),
      encodings::SUI => instructions::execute_sui(&mut self.env, byte),
      encodings::SBI => instructions::execute_sbi(&mut self.env, byte),
      encodings::ORI => instructions::execute_ori(&mut self.env, byte),
      encodings::ANI => instructions::execute_ani(&mut self.env, byte),
      encodings::XRI => instructions::execute_xri(&mut self.env, byte),
      encodings::RLC => instructions::execute_rlc(&mut self.env, byte),
      encodings::RRC => instructions::execute_rrc(&mut self.env, byte),
      encodings::RAR => instructions::execute_rar(&mut self.env, byte),
      encodings::RAL => instructions::execute_ral(&mut self.env, byte),
      encodings::CMA => instructions::execute_cma(&mut self.env, byte),
      encodings::CMC => instructions::execute_cmc(&mut self.env, byte),
      encodings::DAA => instructions::execute_daa(&mut self.env, byte),
      encodings::CPI => instructions::execute_cpi(&mut self.env, byte),
      // Special d8 operand that only takes a value between 0-8
      encodings::RST_0
      | encodings::RST_1
      | encodings::RST_2
      | encodings::RST_3
      | encodings::RST_4
      | encodings::RST_5
      | encodings::RST_6
      | encodings::RST_7 => instructions::execute_rst(&mut self.env, byte),

      // No operands
      encodings::STC => instructions::execute_stc(&mut self.env, byte),
      encodings::XCHG => instructions::execute_xchg(&mut self.env, byte),
      encodings::XTHL => instructions::execute_xthl(&mut self.env, byte),
      encodings::SPHL => instructions::execute_sphl(&mut self.env, byte),
      encodings::PCHL => instructions::execute_pchl(&mut self.env, byte),
      encodings::RM => instructions::execute_rm(&mut self.env, byte),
      encodings::RP => instructions::execute_rp(&mut self.env, byte),
      encodings::RZ => instructions::execute_rz(&mut self.env, byte),
      encodings::RC => instructions::execute_rc(&mut self.env, byte),
      encodings::RNZ => instructions::execute_rnz(&mut self.env, byte),
      encodings::RNC => instructions::execute_rnc(&mut self.env, byte),
      encodings::RPO => instructions::execute_rpo(&mut self.env, byte),
      encodings::RPE => instructions::execute_rpe(&mut self.env, byte),
      encodings::RET => instructions::execute_ret(&mut self.env, byte),
      encodings::NOP => instructions::execute_nop(&mut self.env, byte),
      encodings::HLT => instructions::execute_hlt(&mut self.env, byte),

      b => panic!(
        "0x{:X}: invalid instruction received: 0x{:X}",
        self.env.registers.pc, b
      ),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::Interpreter;
  use lexer::Flags;
  use types::{AssembleError, AssembleErrorKind, AssembleResult};

  /// Runs an assembly file, making sure that the expected memory values are set.
  macro_rules! run_file {
      (
          $src:literal,
          [$($write_addr:literal => $write_value:literal),*],
          [$($expect_addr:literal => $expect_value:literal),*]
      ) => {
        {
          let r: AssembleResult<Interpreter> = {
            let src = include_str!(concat!("../../test_files/", $src, ".asm"));
            let mut int = Interpreter::new(parser::parse(src).unwrap());

            if let Err(e) = int.assemble() {
               Err(e)
            } else {
              $(
                int.env.write_memory($write_addr, $write_value);
              )*

              while int.execute().is_some() {}

              $(
                assert_eq!(int.env.memory_at($expect_addr), $expect_value);
              )*

              Ok(int)
            }
          };

          r
        }
      };
      (
          $int:expr,
          [$($write_addr:literal => $write_value:literal),*],
          [$($expect_addr:literal => $expect_value:literal),*]
      ) => {
        {
          $(
            int.env.set_memory_at($write_addr, $write_value);
          )*

          while int.execute().is_some() {}

          $(
            assert_eq!(int.env.memory_at($expect_addr), Some($expect_value));
          )*
        }
      };
  }

  /// Runs an assembly program
  macro_rules! run_asm {
    ($src:literal, $func:expr, $err:literal) => {{
      let r: AssembleResult<()> = {
        let mut int = Interpreter::new(parser::parse($src).unwrap());

        if let Err(e) = int.assemble() {
          Err(e)
        } else {
          while int.execute().is_some() {}

          assert!($func(&mut int), $err);

          Ok(())
        }
      };

      r
    }};
  }

  #[test]
  fn using_dollar_sign_as_operand() {
    run_asm!(
      "LXI B, $\nHLT",
      |int: &mut Interpreter| int.env.registers.b == 0x0 && int.env.registers.c == 0x0,
      "expected LXI to work with $"
    )
    .unwrap();

    run_asm!(
      "NOP\nLXI B, $\nHLT",
      |int: &mut Interpreter| int.env.registers.b == 0x0 && int.env.registers.c == 0x1,
      "expected LXI to work with $"
    )
    .unwrap();

    run_asm!(
      "LXI B, $ + 6\nNOP\nNOP\nNOP\nHLT",
      |int: &mut Interpreter| int.env.registers.b == 0x0 && int.env.registers.c == 0x6,
      "expected LXI to work with $ as an expression"
    )
    .unwrap();

    run_asm!(
      "LXI H, $ + 6\nNOP\nNOP\nMOV A, M\nHLT",
      |int: &mut Interpreter| int.env.registers.h == 0x0
        && int.env.registers.l == 0x6
        && int.env.registers.a == 0x7F,
      "expected LXI to work with $ as an expression and HLT instruction to be loaded"
    )
    .unwrap();
  }

  #[test]
  fn lxi_d16_operands() {
    run_asm!(
      "LXI B, FOO\nFOO:\nHLT",
      |int: &mut Interpreter| int.env.registers.b == 0x0 && int.env.registers.c == 0x5,
      "expected LXI to work with future defined label"
    )
    .unwrap();

    run_asm!(
      "FOO:\nNOP\nLXI B, FOO\nHLT",
      |int: &mut Interpreter| int.env.registers.b == 0x0 && int.env.registers.c == 0x2,
      "expected LXI to work with previously defined label"
    )
    .unwrap();

    assert_eq!(
      run_asm!(
        "LXI B, FOO\nHLT",
        |_| false,
        "expected LXI to not work with undefined labels"
      )
      .map_err(|x| x.kind),
      Err(AssembleErrorKind::IdentifierNotDefined)
    );

    run_asm!(
      "LXI B,'AB'\nHLT",
      |int: &mut Interpreter| int.env.registers.b == b'A' && int.env.registers.c == b'B',
      "expected LXI to work 2 byte string"
    )
    .unwrap();

    run_asm!(
      "LXI B,'AB' + 5\nHLT",
      |int: &mut Interpreter| {
        let data = ((b'A' as u16) << 8 | b'B' as u16) + 5;

        int.env.registers.b == (data >> 8) as u8 && int.env.registers.c == data as u8
      },
      "expected LXI to work 2 byte string expression"
    )
    .unwrap();
  }

  #[test]
  fn mvi_operands() {
    assert_eq!(
      run_asm!("MVI A, BOO", |_| false, "using identifier as d8 operand"),
      Err(AssembleError::new(
        7,
        AssembleErrorKind::IdentifierNotDefined
      )),
      "using identifier as d8 operand"
    );

    run_asm!(
      "MVI A, 'B'",
      |int: &mut Interpreter| int.env.registers.a == b'B',
      "using string for d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 0FFH",
      |int: &mut Interpreter| int.env.registers.a == u8::MAX,
      "using u8::MAX for d8"
    )
    .unwrap();

    assert_eq!(
      run_asm!("MVI A, 'BOO'", |_| false, "using multi byte string for d8"),
      Err(AssembleError::new(
        7,
        AssembleErrorKind::ExpectedOneByteValue
      )),
      "using multi byte string for d8"
    );

    assert_eq!(
      run_asm!("MVI A, -0FFFFH", |_| false, "using negative u16 for d8"),
      Err(AssembleError::new(
        7,
        AssembleErrorKind::ExpectedOneByteValue
      )),
      "using negative u16 for d8"
    );

    assert_eq!(
      run_asm!(
        "MVI A, 0FFFFH",
        |_| false,
        "using d16 operand instead of d8"
      ),
      Err(AssembleError::new(
        7,
        AssembleErrorKind::ExpectedOneByteValue
      )),
      "using d16 instead of d8"
    );
  }

  #[test]
  fn d8_operands() {
    run_asm!(
      "MVI A, 01000001B\nMVI B, 'A'\nMVI C, 41H\nMVI D, 101Q\nMVI E, 65\
\nMVI H, 5 + 30 * 2\nMVI L, 5 + (-30 * -2)",
      |int: &mut Interpreter| {
        [
          int.env.registers.a,
          int.env.registers.b,
          int.env.registers.c,
          int.env.registers.d,
          int.env.registers.e,
          int.env.registers.h,
          int.env.registers.l,
        ]
        .iter()
        .all(|x| *x == b'A')
      },
      "MVI w/ 'A' d8"
    )
    .unwrap();
  }

  #[test]
  fn one_byte_ascii_operands() {
    run_asm!(
      "MVI B, 'A'",
      |int: &mut Interpreter| int.env.registers.b == b'A',
      "invalid MVI w/ d8"
    )
    .unwrap();

    run_asm!(
      "STC\nMVI A, 03H\nACI 'A'",
      |int: &mut Interpreter| int.env.registers.a == b'A' + 0x3 + 0x1,
      "invalid ACI w/ d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 50H\nSBI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x50 - b'A',
      "invalid SBI w/ d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 03H\nXRI 'A'",
      |int: &mut Interpreter| int.env.registers.a == b'A' ^ 0x3,
      "invalid XRI w/ d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 03H\nCPI 'A'",
      |int: &mut Interpreter| int.env.is_flag_set(Flags::Carry) && int.env.is_flag_set(Flags::Sign),
      "invalid CPI w/ d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 03H\nADI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x3 + b'A',
      "invalid ADI w/ d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 68H\nSUI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x68 - b'A',
      "invalid SUI with d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 03H\nANI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x3 & b'A',
      "invalid ANI w/ d8"
    )
    .unwrap();

    run_asm!(
      "MVI A, 03H\nORI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x3 | b'A',
      "invalid ORI w/ d8"
    )
    .unwrap();
  }

  // Test files
  #[test]
  fn even_numbers_in_array() {
    run_file!(
      "even_numbers_in_array",
      [
        0x2040 => 0x1, 0x2041 => 0x2, 0x2042 => 0x3, 0x2043 => 0x4, 0x2044 => 0xA,
        0x2045 => 0x5, 0x2046 =>  0x60
      ],
      [0x2070 => 0x4]
    )
    .unwrap();
  }

  #[test]
  fn pos_or_neg() {
    // Test a positive number
    let mut interpreter = run_file!(
      "pos_or_neg", [0x2050 => 0x17], [0x2055 => 0x0]
    )
    .unwrap();

    interpreter.reset(false);

    // Test a negative number
    run_file!(
      "pos_or_neg", [0x2050 => 0xD6], [0x2055 => 0x1]
    )
    .unwrap();
  }

  #[test]
  fn sum_of_array() {
    run_file!(
      "sum_of_array",
      [0x02050 => 0x1, 0x2051 => 0x2, 0x2052 => 0x3, 0x2053 => 0x04, 0x2054 => 0xA],
      [0x3000 => 0x14, 0x3001 => 0x0]
    )
    .unwrap();
  }

  #[test]
  fn ones_comp() {
    run_file!("ones_complement", [], [0x50 => 0x7A]).unwrap();
  }

  #[test]
  fn twos_comp() {
    run_file!("twos_complement", [], [0x50 => 0x9B]).unwrap();
  }

  #[test]
  fn add_two_bytes() {
    run_file!("add_two_bytes", [0x2000 => 0x10, 0x2001 => 0x10], [0x2002 => 0x20]).unwrap();
  }

  #[test]
  fn max_array_value() {
    run_file!("max_array_value", [0x0050 => 0x92, 0x0051 => 0xB4], [0x0060 => 0xB4]).unwrap();
  }

  #[test]
  fn num_zeros_in_byte() {
    run_file!("num_zeros_in_byte", [0x0030 => 0xF2], [0x0040 => 0x3]).unwrap();
  }

  #[test]
  fn min_num_in_n_array() {
    run_file!("min_num_in_n_array",
      [
        0x0030 => 0x6, 0x0031 => 0xB4, 0x0032 => 0x56, 0x0033 => 0x8,
        0x0034 => 0x45, 0x0035 => 0x33, 0x0036 => 0x7
      ],
      [0x0040 => 0x7]
    )
    .unwrap();
  }

  #[test]
  fn occurrences_of_num() {
    run_file!(
      "occurrences_of_num",
      [
        0x0040 => 0x1, 0x0041 => 0x2, 0x0042 => 0x1, 0x0043 => 0x3,
        0x0044 => 0x8, 0x0045 => 0x1, 0x0046 => 0xA2,
        // Search for 0x1
        0x0060 => 0x1
      ],
      [0x0070 => 0x3]
    )
    .unwrap();
  }
}
