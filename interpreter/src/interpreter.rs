use crate::{instruction_bytes_occupied, instructions, Environment};
use parser::nodes::{Node, ProgramNode};
use types::AssemblerError;

#[derive(Debug)]
pub struct Interpreter {
  node: ProgramNode,
  assemble_index: u16,
  env: Environment,
}

impl Interpreter {
  pub fn new(ast: ProgramNode) -> Self {
    Self {
      node: ast,
      assemble_index: 0,
      env: Environment::new(),
    }
  }

  /// Assmebles the assembly, encoding the instructions into memory.
  pub fn assemble(&mut self) -> types::AssemblerResult<()> {
    let mut unassembled = Vec::new();

    for node in self.node.children() {
      match node {
        Node::Instruction(insn) => {
          self
            .env
            .encode_instruction(self.assemble_index, insn, &mut unassembled);

          self.assemble_index += instruction_bytes_occupied(&insn.instruction()) as u16;
        }
        Node::Label(label) => {
          let label_name = label.label_name();

          if self.env.labels.contains_key(&label_name) {
            return Err(AssemblerError::LabelRedefined);
          }

          // The label is to be inserted at the current address will be the address to go to
          let lower = (self.assemble_index & 0xFF) as u8;
          let upper = (self.assemble_index >> 8) as u8;

          let addr = Environment::INSTRUCTION_STARTING_ADDRESS + self.assemble_index;

          self.env.assemble_instruction(addr, lower);
          self.env.assemble_instruction(addr + 1, upper);
          // Make this index (and the next) as a label index
          self.env.label_indices.insert(addr, label_name.clone());

          self.assemble_index += 2;

          // Point this label to the instruction's that should be executed
          self.env.add_label(label_name, self.assemble_index);
        }
      };
    }

    // It's okay to create a new vec since we expect to have everything assembled after this second pass.
    let mut new_unassembled = vec![];

    if !unassembled.is_empty() {
      for elem in unassembled.iter() {
        self
          .env
          .encode_instruction(elem.1, elem.0, &mut new_unassembled);
      }
    }

    for n in 0..30 {
      eprintln!("0x{:X}: 0x{:X}", n, self.env.memory_at(n));
    }

    // TODO: Change this to an error
    assert_eq!(new_unassembled.len(), 0);

    Ok(())
  }

  /// Resets the interpreter, wiping all memory and registers.
  ///
  /// If `wipe_encoded` is `false`, then the assembled instructions in memory are preserved.
  pub fn reset(&mut self, wipe_encoded: bool) {
    if wipe_encoded {
      self.env.reset(0);
      self.assemble_index = 0;
    } else {
      self.env.reset(self.assemble_index);
    }
  }

  fn fetch_instruction(&mut self) -> Option<u8> {
    if self.env.registers.pc >= self.assemble_index {
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
      // ARITHMETIC INSTRUCTIONS
      // DCX
      b if matches!(b, 0x0B | 0x1B | 0x2B | 0x3B) => instructions::execute_dcx(&mut self.env, b),
      // DAD
      b if matches!(b, 0x09 | 0x19 | 0x29 | 0x39) => instructions::execute_dad(&mut self.env, b),
      // DCR
      b if matches!(b, 0x05 | 0x15 | 0x25 | 0x35 | 0x0D | 0x1D | 0x2D | 0x3D) => {
        instructions::execute_dcr(&mut self.env, b)
      }
      // INR
      b if matches!(b, 0x04 | 0x14 | 0x24 | 0x34 | 0x0C | 0x1C | 0x2C | 0x3C) => {
        instructions::execute_inr(&mut self.env, b)
      }
      // INX
      b if matches!(b, 0x03 | 0x13 | 0x23 | 0x33) => instructions::execute_inx(&mut self.env, b),
      // SBB
      b if b >= 0x98 && b <= 0x9F => instructions::execute_sbb(&mut self.env, b),
      // SUB
      b if b >= 0x90 && b <= 0x97 => instructions::execute_sub(&mut self.env, b),
      // ADC
      b if b >= 0x88 && b <= 0x8F => instructions::execute_adc(&mut self.env, b),
      // SUI imm 8
      b if b == 0xD6 => instructions::execute_sui(&mut self.env, b),
      // ADI imm8
      b if b == 0xC6 => instructions::execute_adi(&mut self.env, b),
      // ADD
      b if b >= 0x80 && b <= 0x87 => instructions::execute_add(&mut self.env, b),
      // SBI imm8
      b if b == 0xDE => instructions::execute_sbi(&mut self.env, b),
      // ACI
      b if b == 0xCE => instructions::execute_aci(&mut self.env, b),
      // RLC
      b if b == 0x07 => instructions::execute_rlc(&mut self.env, b),
      // RRC
      b if b == 0x0F => instructions::execute_rrc(&mut self.env, b),
      // RAR
      b if b == 0x1F => instructions::execute_rar(&mut self.env, b),
      // RAL
      b if b == 0x17 => instructions::execute_ral(&mut self.env, b),
      // CMA
      b if b == 0x2F => instructions::execute_cma(&mut self.env, b),
      // CMC
      b if b == 0x3F => instructions::execute_cmc(&mut self.env, b),
      // DAA
      b if b == 0x27 => instructions::execute_daa(&mut self.env, b),

      // DATA TRANSFER INSTRUCTIONS
      // MOV r1, r2
      b if b >= 0x40 && b <= 0x7F && b != 0x76 => instructions::execute_mov(&mut self.env, b),
      // MVI r1, imm8
      b if matches!(b, 0x06 | 0x16 | 0x26 | 0x36 | 0x0E | 0x1E | 0x2E | 0x3E) => {
        instructions::execute_mvi(&mut self.env, b)
      }
      // LHLD imm16
      b if b == 0x2A => instructions::execute_lhld(&mut self.env, b),
      // LDAX
      b if matches!(b, 0x0A | 0x1A) => instructions::execute_ldax(&mut self.env, b),
      // LDA imm16
      b if b == 0x3A => instructions::execute_lda(&mut self.env, b),
      // STAX
      b if matches!(b, 0x02 | 0x12) => instructions::execute_stax(&mut self.env, b),
      // STA imm16
      b if b == 0x32 => instructions::execute_sta(&mut self.env, b),
      // SHLD im16
      b if b == 0x22 => instructions::execute_shld(&mut self.env, b),
      // LXI r1, imm16
      b if matches!(b, 0x01 | 0x11 | 0x21 | 0x31) => instructions::execute_lxi(&mut self.env, b),
      // XCHG
      b if b == 0xEB => instructions::execute_xchg(&mut self.env, b),
      // XTHL
      b if b == 0xE3 => instructions::execute_xthl(&mut self.env, b),
      // SPHL
      b if b == 0xF9 => instructions::execute_sphl(&mut self.env, b),
      // PCHL
      b if b == 0xE9 => instructions::execute_pchl(&mut self.env, b),

      // LOGICAL INSTRUCTIONS
      // ORA
      b if b >= 0xB0 && b <= 0xB7 => instructions::execute_ora(&mut self.env, b),
      // XRA
      b if b >= 0xA8 && b <= 0xAF => instructions::execute_xra(&mut self.env, b),
      // ANA
      b if b >= 0xA0 && b <= 0xA7 => instructions::execute_ana(&mut self.env, b),
      // ORI imm8
      b if b == 0xF6 => instructions::execute_ori(&mut self.env, b),
      // ANI imm8
      b if b == 0xE6 => instructions::execute_ani(&mut self.env, b),
      // XRI imm8
      b if b == 0xEE => instructions::execute_xri(&mut self.env, b),

      // BRANCHING INSTRUCTIONS
      // RNZ
      b if b == 0xC0 => instructions::execute_rnz(&mut self.env, b),
      // RNC
      b if b == 0xD0 => instructions::execute_rnc(&mut self.env, b),
      // RPO
      b if b == 0xE0 => instructions::execute_rpo(&mut self.env, b),
      // RP
      b if b == 0xF0 => instructions::execute_rp(&mut self.env, b),
      // RZ
      b if b == 0xC8 => instructions::execute_rz(&mut self.env, b),
      // RC
      b if b == 0xD8 => instructions::execute_rc(&mut self.env, b),
      // RPE
      b if b == 0xE8 => instructions::execute_rpe(&mut self.env, b),
      // RM
      b if b == 0xF8 => instructions::execute_rm(&mut self.env, b),
      // RET
      b if b == 0xC9 => instructions::execute_ret(&mut self.env, b),
      // CALL label
      b if b == 0xCD => instructions::execute_call(&mut self.env, b),
      // CM label
      b if b == 0xFC => instructions::execute_cm(&mut self.env, b),
      // CPE label
      b if b == 0xEC => instructions::execute_cpe(&mut self.env, b),
      // CC label
      b if b == 0xDC => instructions::execute_cc(&mut self.env, b),
      // CZ label
      b if b == 0xCC => instructions::execute_cz(&mut self.env, b),
      // CP label
      b if b == 0xF4 => instructions::execute_cp(&mut self.env, b),
      // CPO label
      b if b == 0xE4 => instructions::execute_cpo(&mut self.env, b),
      // CNC label
      b if b == 0xD4 => instructions::execute_cnc(&mut self.env, b),
      // CNZ label
      b if b == 0xC4 => instructions::execute_cnz(&mut self.env, b),
      // JM label
      b if b == 0xFA => instructions::execute_jm(&mut self.env, b),
      // JPE label
      b if b == 0xEA => instructions::execute_jpe(&mut self.env, b),
      // JC label
      b if b == 0xDA => instructions::execute_jc(&mut self.env, b),
      // JZ label
      b if b == 0xCA => instructions::execute_jz(&mut self.env, b),
      // JMP label
      b if b == 0xC3 => instructions::execute_jmp(&mut self.env, b),
      // JP label
      b if b == 0xF2 => instructions::execute_jp(&mut self.env, b),
      // JPO label
      b if b == 0xE2 => instructions::execute_jpo(&mut self.env, b),
      // JNC label
      b if b == 0xD2 => instructions::execute_jnc(&mut self.env, b),
      // JNZ label
      b if b == 0xC2 => instructions::execute_jnz(&mut self.env, b),
      // CMP
      b if b >= 0xB8 && b <= 0xBF => instructions::execute_cmp(&mut self.env, b),
      // CPI imm8
      b if b == 0xFE => instructions::execute_cpi(&mut self.env, b),

      // MANIPULATING INSTRUCTIONS
      // PUSH
      b if matches!(b, 0xC5 | 0xD5 | 0xE5 | 0xF5) => instructions::execute_push(&mut self.env, b),
      // POP
      b if matches!(b, 0xC1 | 0xD1 | 0xE1 | 0xF1) => instructions::execute_pop(&mut self.env, b),
      // STC
      b if matches!(b, 0x37) => instructions::execute_stc(&mut self.env, b),
      // RST
      b if matches!(b, 0xC7 | 0xD7 | 0xE7 | 0xF7 | 0xCF | 0xDF | 0xEF | 0xFF) => {
        instructions::execute_rst(&mut self.env, b)
      }
      // NOP
      0x0 => instructions::execute_nop(&mut self.env, 0x0),
      // HLT
      0x76 => instructions::execute_hlt(&mut self.env, 0x76),

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

  /// Runs an assembly file, making sure that the expected memory values are set.
  macro_rules! run_file {
      (
          $src:literal,
          [$($write_addr:literal => $write_value:literal),*],
          [$($expect_addr:literal => $expect_value:literal),*]
      ) => {
        {
          let src = include_str!(concat!("../../test_files/", $src, ".asm"));
          let mut int = Interpreter::new(parser::parse(src).unwrap());

          int.assemble().unwrap();

          $(
            int.env.write_memory($write_addr, $write_value);
          )*

          while int.execute().is_some() {}

          $(
            assert_eq!(int.env.memory_at($expect_addr), $expect_value);
          )*

          int
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
    (
          $src:literal,
          $func:expr,
          $err:literal
      ) => {
      let mut int = Interpreter::new(parser::parse($src).unwrap());

      int.assemble().unwrap();

      while int.execute().is_some() {}

      assert!($func(&mut int));
    };
  }

  #[test]
  fn d8_operands() {
    run_asm!(
      "MVI B, 'A'",
      |int: &mut Interpreter| int.env.registers.b == b'A',
      "invalid MVI w/ d8"
    );

    run_asm!(
      "STC\nMVI A, 03H\nACI 'A'",
      |int: &mut Interpreter| int.env.registers.a == b'A' + 0x3 + 0x1,
      "invalid ACI w/ d8"
    );

    run_asm!(
      "MVI A, 50H\nSBI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x50 - b'A',
      "invalid SBI w/ d8"
    );
    run_asm!(
      "MVI A, 03H\nXRI 'A'",
      |int: &mut Interpreter| int.env.registers.a == b'A' ^ 0x3,
      "invalid XRI w/ d8"
    );
    run_asm!(
      "MVI A, 03H\nCPI 'A'",
      |int: &mut Interpreter| int.env.is_flag_set(Flags::Carry) && int.env.is_flag_set(Flags::Sign),
      "invalid CPI w/ d8"
    );

    run_asm!(
      "MVI A, 03H\nADI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x3 + b'A',
      "invalid ADI w/ d8"
    );
    run_asm!(
      "MVI A, 68H\nSUI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x68 - b'A',
      "invalid SUI with d8"
    );
    run_asm!(
      "MVI A, 03H\nANI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x3 & b'A',
      "invalid ANI w/ d8"
    );
    run_asm!(
      "MVI A, 03H\nORI 'A'",
      |int: &mut Interpreter| int.env.registers.a == 0x3 | b'A',
      "invalid ORI w/ d8"
    );
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
    );
  }

  #[test]
  fn pos_or_neg() {
    // Test a positive number
    let mut interpreter = run_file!(
      "pos_or_neg", [0x2050 => 0x17], [0x2055 => 0x0]
    );

    interpreter.reset(false);

    // Test a negative number
    run_file!(
      "pos_or_neg", [0x2050 => 0xD6], [0x2055 => 0x1]
    );
  }

  #[test]
  fn sum_of_array() {
    run_file!(
      "sum_of_array",
      [0x02050 => 0x1, 0x2051 => 0x2, 0x2052 => 0x3, 0x2053 => 0x04, 0x2054 => 0xA],
      [0x3000 => 0x14, 0x3001 => 0x0]
    );
  }

  #[test]
  fn ones_comp() {
    run_file!("ones_complement", [], [0x50 => 0x7A]);
  }

  #[test]
  fn twos_comp() {
    run_file!("twos_complement", [], [0x50 => 0x9B]);
  }

  #[test]
  fn add_two_bytes() {
    run_file!("add_two_bytes", [0x2000 => 0x10, 0x2001 => 0x10], [0x2002 => 0x20]);
  }

  #[test]
  fn max_array_value() {
    run_file!("max_array_value", [0x0050 => 0x92, 0x0051 => 0xB4], [0x0060 => 0xB4]);
  }

  #[test]
  fn num_zeros_in_byte() {
    run_file!("num_zeros_in_byte", [0x0030 => 0xF2], [0x0040 => 0x3]);
  }

  #[test]
  fn min_num_in_n_array() {
    run_file!("min_num_in_n_array",
      [
        0x0030 => 0x6, 0x0031 => 0xB4, 0x0032 => 0x56, 0x0033 => 0x8,
        0x0034 => 0x45, 0x0035 => 0x33, 0x0036 => 0x7
      ],
      [0x0040 => 0x7]
    );
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
    );
  }
}
