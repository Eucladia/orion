// TODO: Make arithmetic ops wrapping
// TODO: Bounds checking for memory and return a result
use crate::{instruction_bytes_occupied, Environment};
use lexer::{Flags, Register};
use parser::nodes::{Node, ProgramNode};

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
  pub fn assemble(&mut self) -> crate::InterpreterResult<()> {
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
          // The label is to be inserted at the current address will be the address to go to
          let lower = (self.assemble_index & 0xFF) as u8;
          let upper = (self.assemble_index >> 8) as u8;

          let addr = Environment::INSTRUCTION_STARTING_ADDRESS + self.assemble_index;
          let label_name = label.label_name();

          self.env.assemble_instruction_unchecked(addr, lower);
          self.env.assemble_instruction_unchecked(addr + 1, upper);
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
      eprintln!("0x{:X}: 0x{:X}", n, self.env.memory_at(n).unwrap());
    }

    // TODO: Change this to an error
    assert_eq!(new_unassembled.len(), 0);

    Ok(())
  }

  fn fetch_instruction(&mut self) -> Option<u8> {
    if self.env.registers.pc >= self.assemble_index {
      return None;
    }

    Some(self.env.memory_at(self.env.registers.pc)?)
  }

  /// Execute's the next instruction in memory.
  pub fn execute(&mut self) -> Option<()> {
    let fetched = self.fetch_instruction()?;

    self.execute_instruction(fetched);

    Some(())
  }

  /// Decodes a byte into an [lexer::instruction::Instruction].
  ///
  /// Returns [None] if the byte was a label
  fn execute_instruction(&mut self, byte: u8) {
    if self.env.label_indices.contains_key(&self.env.registers.pc) {
      // Labels are 16 bits
      self.env.registers.pc += 2;
    }

    match byte {
      // MOV r1, r2
      b if b >= 0x40 && b <= 0x7F && b != 0x76 => execute_mov(&mut self.env, b),

      // MVI r1, imm8
      b if matches!(b, 0x06 | 0x16 | 0x26 | 0x36 | 0x0E | 0x1E | 0x2E | 0x3E) => {
        execute_mvi(&mut self.env, b)
      }

      // LXI r1, imm16
      b if matches!(b, 0x01 | 0x11 | 0x21) => execute_lxi(&mut self.env, b),

      // CALL label
      b if b == 0xCD => execute_call(&mut self.env, b),

      // CM label
      b if b == 0xFC => execute_cm(&mut self.env, b),

      // CPE label
      b if b == 0xEC => execute_cpe(&mut self.env, b),
      // CC label
      b if b == 0xDC => execute_cc(&mut self.env, b),

      // CZ label
      b if b == 0xCC => execute_cz(&mut self.env, b),

      // CP label
      b if b == 0xF4 => execute_cp(&mut self.env, b),

      // CPO label
      b if b == 0xE4 => execute_cpo(&mut self.env, b),

      // CNC label
      b if b == 0xD4 => execute_cnc(&mut self.env, b),

      // CNZ label
      b if b == 0xC4 => execute_cnz(&mut self.env, b),

      // JM label
      b if b == 0xFA => execute_jm(&mut self.env, b),

      // JPE label
      b if b == 0xEA => execute_jpe(&mut self.env, b),

      // JC label
      b if b == 0xDA => execute_jc(&mut self.env, b),

      // JZ label
      b if b == 0xCA => execute_jz(&mut self.env, b),

      // JMP label
      b if b == 0xC3 => execute_jmp(&mut self.env, b),

      // JP label
      b if b == 0xF2 => execute_jp(&mut self.env, b),

      // JPO label
      b if b == 0xE2 => execute_jpo(&mut self.env, b),

      // JNC label
      b if b == 0xD2 => execute_jnc(&mut self.env, b),

      // JNZ label
      b if b == 0xC2 => execute_jnz(&mut self.env, b),

      // LHLD imm16
      b if b == 0x2A => execute_lhld(&mut self.env, b),

      // LDAX
      b if matches!(b, 0x0A | 0x1A) => execute_ldax(&mut self.env, b),

      // LDA imm16
      b if b == 0x3A => execute_lda(&mut self.env, b),

      // STAX
      b if matches!(b, 0x02 | 0x12) => execute_stax(&mut self.env, b),

      // STA imm16
      b if b == 0x32 => execute_sta(&mut self.env, b),

      // SHLD im16
      b if b == 0x22 => execute_shld(&mut self.env, b),

      // PUSH
      b if matches!(b, 0xC5 | 0xD5 | 0xE5 | 0xF5) => execute_push(&mut self.env, b),

      // POP
      b if matches!(b, 0xC1 | 0xD1 | 0xE1 | 0xF1) => execute_pop(&mut self.env, b),

      // DCX
      b if matches!(b, 0x0B | 0x1B | 0x2B | 0x3B) => execute_dcx(&mut self.env, b),

      // DAD
      b if matches!(b, 0x09 | 0x19 | 0x29 | 0x39) => execute_dad(&mut self.env, b),

      // DCR
      b if matches!(b, 0x05 | 0x15 | 0x25 | 0x35 | 0x0D | 0x1D | 0x2D | 0x3D) => {
        execute_dcr(&mut self.env, b)
      }

      // INR
      b if matches!(b, 0x04 | 0x14 | 0x24 | 0x34 | 0x0C | 0x1C | 0x2C | 0x3C) => {
        execute_inr(&mut self.env, b)
      }

      // INX
      b if matches!(b, 0x03 | 0x13 | 0x23 | 0x33) => execute_inx(&mut self.env, b),

      // CMP
      b if b >= 0xB8 && b <= 0xBF => execute_cmp(&mut self.env, b),

      // ORA
      b if b >= 0xB0 && b <= 0xB7 => execute_ora(&mut self.env, b),

      // XRA
      b if b >= 0xA8 && b <= 0xAF => execute_xra(&mut self.env, b),

      // ANA
      b if b >= 0xA0 && b <= 0xA7 => execute_ana(&mut self.env, b),

      // SBB
      b if b >= 0x98 && b <= 0x9F => execute_sbb(&mut self.env, b),

      // SUB
      b if b >= 0x90 && b <= 0x97 => execute_sub(&mut self.env, b),

      // ADC
      b if b >= 0x88 && b <= 0x8F => execute_adc(&mut self.env, b),

      // ORI imm8
      b if b == 0xF6 => execute_ori(&mut self.env, b),

      // ANI imm8
      b if b == 0xE6 => execute_ani(&mut self.env, b),

      // SUI imm 8
      b if b == 0xD6 => execute_sui(&mut self.env, b),

      // ADI imm8
      b if b == 0xC6 => execute_adi(&mut self.env, b),

      // ADD
      b if b >= 0x80 && b <= 0x87 => execute_add(&mut self.env, b),

      // CPI imm8
      b if b == 0xFE => execute_cpi(&mut self.env, b),

      // XRI imm8
      b if b == 0xEE => execute_xri(&mut self.env, b),

      // SBI imm8
      b if b == 0xDE => execute_sbi(&mut self.env, b),

      // ACI
      b if b == 0xCE => execute_aci(&mut self.env, b),

      // NOP
      0x00 => self.env.registers.pc += 1,

      // RLC
      b if b == 0x07 => execute_rlc(&mut self.env, b),

      // RRC
      b if b == 0x0F => execute_rrc(&mut self.env, b),

      // RAR
      b if b == 0x1F => execute_rar(&mut self.env, b),

      // CMA
      b if b == 0x2F => execute_cma(&mut self.env, b),

      // CMC
      b if b == 0x3F => execute_cmc(&mut self.env, b),

      // HLT
      0x76 => self.env.registers.pc += 1,

      // RNZ
      b if b == 0xC0 => execute_rnz(&mut self.env, b),

      // RNC
      b if b == 0xD0 => execute_rnc(&mut self.env, b),

      // RPO
      b if b == 0xE0 => execute_rpo(&mut self.env, b),

      // RP
      b if b == 0xF0 => execute_rp(&mut self.env, b),

      // RZ
      b if b == 0xC8 => execute_rz(&mut self.env, b),

      // RC
      b if b == 0xD8 => execute_rc(&mut self.env, b),

      // RPE
      b if b == 0xE8 => execute_rpe(&mut self.env, b),

      // RM
      b if b == 0xF8 => execute_rm(&mut self.env, b),

      // RET
      b if b == 0xC9 => execute_ret(&mut self.env, b),

      b => panic!("invalid instruction received: {b}"),
    }
  }
}

fn execute_mov(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let (dest, src) = if instruction_byte == 0x77 {
    (Register::M, Register::A)
  } else {
    let base = instruction_byte - 0x40;

    (decode_register(base / 8), decode_register(base % 8))
  };

  let reg_value = get_register_value(env, src).unwrap();

  set_register_value(env, dest, reg_value);

  env.registers.dr = reg_value as u16;
  env.registers.pc += 1;
}

fn execute_mvi(env: &mut Environment, b: u8) {
  env.registers.ir = b;

  let dest = match b {
    0x06 => Register::B,
    0x16 => Register::D,
    0x26 => Register::H,
    0x36 => Register::M,

    0x0E => Register::C,
    0x1E => Register::C,
    0x2E => Register::C,
    0x3E => Register::C,
    _ => unreachable!(),
  };

  let value = env.memory_at(env.registers.pc + 1).unwrap();

  set_register_value(env, dest, value);

  env.registers.dr = (value as u16) << 8;
  env.registers.pc += 3;
}

fn execute_lxi(env: &mut Environment, byte: u8) {
  env.registers.ir = byte;

  let lower = env.memory_at(env.registers.pc + 1).unwrap();
  let upper = env.memory_at(env.registers.pc + 2).unwrap();

  env.registers.dr = ((lower as u16) << 8) | upper as u16;

  match byte {
    // Register pair B-C
    0x01 => {
      env.registers.b = upper;
      env.registers.c = lower;
    }
    // Register pair D-E
    0x11 => {
      env.registers.d = upper;
      env.registers.e = lower;
    }
    // Register pair H-L
    0x21 => {
      env.registers.h = upper;
      env.registers.l = lower;
    }
    _ => unreachable!(),
  }

  env.registers.pc += 3;
}

fn execute_call(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
  let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
  let jump_to = (label_upper as u16) << 8 | label_lower as u16;

  env.add_to_call_stack(env.registers.pc + 3);
  env.registers.pc = jump_to;
}

fn execute_cm(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Sign) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_cpe(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Parity) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_cc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Carry) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_cz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Zero) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_cp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Sign) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_cpo(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Parity) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_cnc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Carry) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_cnz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Zero) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.add_to_call_stack(env.registers.pc + 3);
    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jm(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Sign) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jpe(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Parity) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Carry) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Zero) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jmp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
  let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
  let jump_to = (label_upper as u16) << 8 | label_lower as u16;

  env.registers.pc = jump_to;
}

fn execute_jp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Sign) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jpo(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Parity) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jnc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Carry) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_jnz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Zero) {
    let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
    let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
    let jump_to = (label_upper as u16) << 8 | label_lower as u16;

    env.registers.pc = jump_to;
  } else {
    env.registers.pc += 3;
  }
}

fn execute_lhld(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.registers.h = env.memory_at(env.registers.pc + 1).unwrap();
  env.registers.l = env.memory_at(env.registers.pc + 2).unwrap();

  env.registers.pc += 3;
}

fn execute_ldax(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x0A {
    let address = (env.registers.b as u16) << 8 | env.registers.c as u16;

    env.registers.a = env.memory_at(address).unwrap();
  } else if instruction_byte == 0x1A {
    let address = (env.registers.d as u16) << 8 | env.registers.e as u16;

    env.registers.a = env.memory_at(address).unwrap();
  }

  env.registers.pc += 1;
}

fn execute_lda(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let lower = env.memory_at(env.registers.pc + 1).unwrap();
  let upper = env.memory_at(env.registers.pc + 2).unwrap();
  let value = env.memory_at((upper as u16) << 8 | lower as u16).unwrap();

  env.registers.a = value;
  env.registers.dr = (lower as u16) << 8 | upper as u16;
  env.registers.pc += 3;
}

fn execute_stax(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x02 {
    let address = (env.registers.b as u16) << 8 | env.registers.c as u16;

    env.set_memory_at(address, env.registers.a);
  } else if instruction_byte == 0x12 {
    let address = (env.registers.d as u16) << 8 | env.registers.e as u16;

    env.set_memory_at(address, env.registers.a);
  }

  env.registers.pc += 1;
}

fn execute_sta(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let lower = env.memory_at(env.registers.pc + 1).unwrap();
  let upper = env.memory_at(env.registers.pc + 2).unwrap();
  let address = (upper as u16) << 8 | lower as u16;

  env.set_memory_at(address, env.registers.a);

  env.registers.dr = (lower as u16) << 8 | (upper as u16);
  env.registers.pc += 3;
}

fn execute_shld(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let lower = env.memory_at(env.registers.pc + 1).unwrap();
  let upper = env.memory_at(env.registers.pc + 2).unwrap();
  let address = (upper as u16) << 8 | lower as u16;

  // SHLD set in inverse order
  env.set_memory_at(address, env.registers.l);
  env.set_memory_at(address + 1, env.registers.h);

  env.registers.pc += 3;
}

fn execute_push(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0xC5 {
    env.registers.dr = (env.registers.c as u16) << 8 | env.registers.b as u16;

    env.set_memory_at(env.registers.sp, env.registers.b);
    env.set_memory_at(env.registers.sp - 1, env.registers.c);
  } else if instruction_byte == 0xD5 {
    env.registers.dr = (env.registers.e as u16) << 8 | env.registers.d as u16;

    env.set_memory_at(env.registers.sp, env.registers.d);
    env.set_memory_at(env.registers.sp - 1, env.registers.e);
  } else if instruction_byte == 0xE5 {
    env.registers.dr = (env.registers.l as u16) << 8 | env.registers.h as u16;

    env.set_memory_at(env.registers.sp, env.registers.h);
    env.set_memory_at(env.registers.sp - 1, env.registers.l);
  } else if instruction_byte == 0xF5 {
    env.registers.dr = (env.flags as u16) << 8 | env.registers.a as u16;

    env.set_memory_at(env.registers.sp, env.registers.a);
    env.set_memory_at(env.registers.sp - 1, env.flags);
  }

  env.registers.sp -= 2;
  env.registers.pc += 1;
}

fn execute_pop(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let lower = env.memory_at(env.registers.sp + 1).unwrap();
  let upper = env.memory_at(env.registers.sp).unwrap();

  env.registers.dr = (lower as u16) << 8 | upper as u16;

  if instruction_byte == 0xC1 {
    env.registers.b = lower;
    env.registers.c = upper;
  } else if instruction_byte == 0xD1 {
    env.registers.d = lower;
    env.registers.e = upper;
  } else if instruction_byte == 0xE1 {
    env.registers.h = lower;
    env.registers.l = upper;
  } else if instruction_byte == 0xF1 {
    env.registers.a = lower;
    env.flags = upper;
  }

  env.registers.sp += 2;
  env.registers.pc += 1;
}

fn execute_dcx(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x0B {
    let curr_value = (env.registers.b as u16) << 8 | env.registers.c as u16;
    let updated_value = curr_value - 1;

    env.registers.b = (updated_value >> 8) as u8;
    env.registers.c = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x1B {
    let curr_value = (env.registers.d as u16) << 8 | env.registers.e as u16;
    let updated_value = curr_value - 1;

    env.registers.d = (updated_value >> 8) as u8;
    env.registers.e = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x2B {
    let curr_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let updated_value = curr_value - 1;

    env.registers.h = (updated_value >> 8) as u8;
    env.registers.l = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x3B {
    let updated_value = env.registers.sp - 1;

    env.registers.b = (updated_value >> 8) as u8;
    env.registers.c = (updated_value & 0xFF) as u8;
  }

  env.registers.pc += 1;
}

fn execute_dad(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x09 {
    let bc_value = (env.registers.b as u16) << 8 | env.registers.c as u16;
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = bc_value + hl_value;

    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  } else if instruction_byte == 0x19 {
    let de_value = (env.registers.d as u16) << 8 | env.registers.e as u16;
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = de_value + hl_value;

    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  } else if instruction_byte == 0x29 {
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = hl_value + hl_value;

    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  } else if instruction_byte == 0x39 {
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = env.registers.sp + hl_value;

    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  }

  env.registers.pc += 1;
}

fn execute_dcr(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let carry = env.is_flag_set(Flags::Carry);

  if instruction_byte == 0x05 {
    env.registers.b -= 1;
    update_flags_u8_arithmetic(env, env.registers.b + 1, env.registers.b, false);
  } else if instruction_byte == 0x15 {
    env.registers.d -= 1;
    update_flags_u8_arithmetic(env, env.registers.d + 1, env.registers.d, false);
  } else if instruction_byte == 0x25 {
    env.registers.h -= 1;
    update_flags_u8_arithmetic(env, env.registers.h + 1, env.registers.h, false);
  } else if instruction_byte == 0x35 {
    let address = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let value = env.memory_at(address).unwrap();

    env.set_memory_at(address, value - 1);
    update_flags_u8_arithmetic(env, value, value - 1, false);
  } else if instruction_byte == 0x0D {
    env.registers.c -= 1;
    update_flags_u8_arithmetic(env, env.registers.c + 1, env.registers.c, false);
  } else if instruction_byte == 0x1D {
    env.registers.e -= 1;
    update_flags_u8_arithmetic(env, env.registers.e + 1, env.registers.e, false);
  } else if instruction_byte == 0x2D {
    env.registers.l -= 1;
    update_flags_u8_arithmetic(env, env.registers.l + 1, env.registers.l, false);
  } else if instruction_byte == 0x3D {
    env.registers.a -= 1;
    update_flags_u8_arithmetic(env, env.registers.a + 1, env.registers.a, false);
  }

  env.set_flag(Flags::Carry, carry);
  env.registers.pc += 1;
}

// Updates flags for 8 bit arithmetical operations
fn update_flags_u8_arithmetic(
  env: &mut Environment,
  old_value: u8,
  new_value: u8,
  is_addition: bool,
) {
  env.set_flag(Flags::Sign, new_value & 0x80 == 1);
  env.set_flag(Flags::Zero, new_value == 0);
  env.set_flag(Flags::Parity, new_value.count_ones() % 2 == 0);

  // Compare the nibbles accordingly depending on the operation we did
  let old_nibble = old_value & 0x0F;
  let new_nibble = new_value & 0x0F;

  if is_addition {
    env.set_flag(Flags::AuxiliaryCarry, old_nibble + new_nibble > 0x0F);
    // If we added, then we should have a carry if the new value is smaller
    env.set_flag(Flags::Carry, new_value < old_value);
  } else {
    env.set_flag(Flags::AuxiliaryCarry, old_nibble < new_nibble);
    // If we subtracted, then we should have a carry if the new value is greater
    env.set_flag(Flags::Carry, new_value > old_value);
  }
}

fn update_flags_u16_arithmetic(
  env: &mut Environment,
  old_value: u16,
  new_value: u16,
  is_addition: bool,
) {
  env.set_flag(Flags::Sign, new_value & 0x80 == 1);
  env.set_flag(Flags::Zero, new_value == 0);
  env.set_flag(Flags::Parity, new_value.count_ones() % 2 == 0);

  // Compare the nibbles accordingly depending on the operation we did
  let old_nibble = old_value & 0x0F;
  let new_nibble = new_value & 0x0F;

  if is_addition {
    env.set_flag(Flags::AuxiliaryCarry, old_nibble + new_nibble > 0x0F);
    // If we added, then we should have a carry if the new value is smaller
    env.set_flag(Flags::Carry, new_value < old_value);
  } else {
    env.set_flag(Flags::AuxiliaryCarry, old_nibble < new_nibble);
    // If we subtracted, then we should have a carry if the new value is greater
    env.set_flag(Flags::Carry, new_value > old_value);
  }
}

fn execute_inr(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let carry = env.is_flag_set(Flags::Carry);

  if instruction_byte == 0x04 {
    env.registers.b += 1;
    update_flags_u8_arithmetic(env, env.registers.b - 1, env.registers.b, true);
  } else if instruction_byte == 0x14 {
    env.registers.d += 1;
    update_flags_u8_arithmetic(env, env.registers.d - 1, env.registers.d, true);
  } else if instruction_byte == 0x24 {
    env.registers.h += 1;
    update_flags_u8_arithmetic(env, env.registers.h - 1, env.registers.h, true);
  } else if instruction_byte == 0x34 {
    let address = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let value = env.memory_at(address).unwrap();

    env.set_memory_at(address, value + 1);
    update_flags_u8_arithmetic(env, value, value + 1, true);
  } else if instruction_byte == 0x0C {
    env.registers.c += 1;
    update_flags_u8_arithmetic(env, env.registers.c - 1, env.registers.c, true);
  } else if instruction_byte == 0x1C {
    env.registers.e += 1;
    update_flags_u8_arithmetic(env, env.registers.e - 1, env.registers.e, true);
  } else if instruction_byte == 0x2C {
    env.registers.l += 1;
    update_flags_u8_arithmetic(env, env.registers.l - 1, env.registers.l, true);
  } else if instruction_byte == 0x3C {
    env.registers.a += 1;
    update_flags_u8_arithmetic(env, env.registers.a - 1, env.registers.a, true);
  }

  // INR doesn't update the carry flag
  env.set_flag(Flags::Carry, carry);
  env.registers.pc += 1;
}

fn execute_inx(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x03 {
    let curr_value = (env.registers.b as u16) << 8 | env.registers.c as u16;
    let updated_value = curr_value + 1;

    env.registers.b = (updated_value >> 8) as u8;
    env.registers.c = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x13 {
    let curr_value = (env.registers.d as u16) << 8 | env.registers.e as u16;
    let updated_value = curr_value + 1;

    env.registers.d = (updated_value >> 8) as u8;
    env.registers.e = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x23 {
    let curr_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let updated_value = curr_value + 1;

    env.registers.h = (updated_value >> 8) as u8;
    env.registers.l = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x33 {
    env.registers.sp += 1;
  }

  env.registers.pc += 1;
}

fn execute_cmp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0xB8);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();

  env.set_flag(Flags::Sign, a < r);
  env.set_flag(Flags::Zero, a == r);
  env.set_flag(Flags::Parity, (a - r).count_ones() % 2 == 0);
  // Compare the lower nibbles
  env.set_flag(Flags::AuxiliaryCarry, (a & 0x0F) < (r & 0x0F));
  env.set_flag(Flags::Carry, a < r);

  env.registers.pc += 1;
}

fn execute_ora(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0xB0);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();
  let res = a | r;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 1;
}

fn execute_xra(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0xA8);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();
  let res = a ^ r;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 1;
}

fn execute_ana(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0xA0);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();
  let res = a & r;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 1;
}

fn execute_sbb(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0x98);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a - r - carry_value;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(
    Flags::AuxiliaryCarry,
    (a & 0x0F) < (r & 0x0F) || (a & 0x0F) < carry_value,
  );
  env.set_flag(Flags::Carry, a < r + carry_value);

  env.registers.a = res;
  env.registers.pc += 1;
}

fn execute_sub(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0x90);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();
  let res = a - r;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, (a & 0x0F) < (r & 0x0F));
  env.set_flag(Flags::Carry, a < r);

  env.registers.a = res;
  env.registers.pc += 1;
}

fn execute_adc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0x88);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a + r + carry_value;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(
    Flags::AuxiliaryCarry,
    // Check if the 5th bit is not set after adding the lower nibbles
    ((a & 0x0F) + (r & 0x0F) + carry_value) & 0x10 != 0,
  );
  env.set_flag(
    Flags::Carry,
    (a as u16 + r as u16 + carry_value as u16) > 0xFF,
  );

  env.registers.a = res;
  env.registers.pc += 1;
}

fn execute_ori(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a | imm8;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 2;
}

fn execute_ani(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a & imm8;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(
    Flags::AuxiliaryCarry,
    (a & 0x0F) & (imm8 & 0x0F) & 0x10 != 0,
  );
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 2;
}

fn execute_sui(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a - imm8;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, (a & 0x0F) < (imm8 & 0x0F));
  env.set_flag(Flags::Carry, a < imm8);

  env.registers.a = res;
  env.registers.pc += 2;
}

fn execute_adi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a + imm8;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, (a & 0x0F) + (imm8 & 0x0F) > 0x0F);
  env.set_flag(Flags::Carry, (a as u16 + imm8 as u16) > 0xFF);

  env.registers.a = res;
  env.registers.pc += 2;
}

fn execute_add(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = decode_register(instruction_byte - 0x80);
  let a = get_register_value(env, Register::A).unwrap();
  let r = get_register_value(env, register).unwrap();
  let res = a + r;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, (a & 0x0F) + (r & 0x0F) > 0x0F);
  env.set_flag(Flags::Carry, (a as u16 + r as u16) > 0xFF);

  env.registers.a = res;
  env.registers.pc += 1;
}

fn execute_cpi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();

  env.set_flag(Flags::Sign, a < imm8);
  env.set_flag(Flags::Zero, a == imm8);
  env.set_flag(Flags::Parity, (a - imm8).count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, (a & 0x0F) < (imm8 & 0x0F));
  env.set_flag(Flags::Carry, a < imm8);

  env.registers.pc += 2;
}

fn execute_xri(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a ^ imm8;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 2;
}

fn execute_sbi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a - imm8;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(Flags::AuxiliaryCarry, (a & 0x0F) < (imm8 & 0x0F));
  env.set_flag(Flags::Carry, a < imm8);

  env.registers.a = res;
  env.registers.pc += 2;
}

fn execute_aci(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a + imm8 + carry_value;

  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);
  env.set_flag(
    Flags::AuxiliaryCarry,
    ((a & 0x0F) + (imm8 & 0x0F) + carry_value) & 0x10 != 0,
  );
  env.set_flag(
    Flags::Carry,
    (a as u16 + imm8 as u16 + carry_value as u16) > 0xFF,
  );

  env.registers.a = res;
  env.registers.pc += 2;
}

fn execute_rlc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let msb = a & 0x80;
  let rotated = a.rotate_left(1);

  env.set_flag(Flags::Carry, msb != 0);

  env.registers.a = rotated;
  env.registers.pc += 2;
}

fn execute_rrc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let lsb = a & 0x01;
  let rotated = a.rotate_right(1);

  env.set_flag(Flags::Carry, lsb != 0);

  env.registers.a = rotated;
  env.registers.pc += 2;
}

fn execute_rar(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = get_register_value(env, Register::A).unwrap();
  let lsb = a & 0x01;
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let rotated = (a >> 1) | (carry_value << 7);

  env.set_flag(Flags::Carry, lsb == 1);
  env.registers.a = rotated;
  env.registers.pc += 1;
}

fn execute_cma(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;
  env.registers.a = !env.registers.a;

  env.registers.pc += 1;
}

fn execute_cmc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;
  env.set_flag(Flags::Carry, !env.is_flag_set(Flags::Carry));

  env.registers.pc += 1;
}

fn execute_rnz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Zero) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_rnc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Carry) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_rpo(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Parity) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_rp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Sign) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_rz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Zero) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_rc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Carry) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_rpe(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Parity) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_rm(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Sign) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

fn execute_ret(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let go_to = env.return_from_call().unwrap();

  env.registers.pc = go_to;
}

fn set_register_value(env: &mut Environment, dest_reg: Register, value: u8) {
  match dest_reg {
    Register::A => env.registers.a = value,
    Register::B => env.registers.b = value,
    Register::C => env.registers.c = value,
    Register::D => env.registers.d = value,
    Register::E => env.registers.e = value,
    Register::H => env.registers.h = value,
    Register::L => env.registers.l = value,

    Register::M => env.set_memory_at(
      env
        .memory_at((env.registers.h as u16) << 8 | env.registers.l as u16)
        .unwrap() as u16,
      value,
    ),
    _ => unreachable!(),
  }
}

fn get_register_value(env: &Environment, reg: Register) -> Option<u8> {
  Some(match reg {
    Register::A => env.registers.a,
    Register::B => env.registers.b,
    Register::C => env.registers.c,
    Register::D => env.registers.d,
    Register::E => env.registers.e,
    Register::H => env.registers.h,
    Register::L => env.registers.l,
    Register::M => env.memory_at((env.registers.h as u16) << 8 | env.registers.l as u16)?,
    _ => unreachable!(),
  })
}

const fn decode_register(byte: u8) -> Register {
  match byte {
    0 => Register::B,
    1 => Register::C,
    2 => Register::D,
    3 => Register::E,
    4 => Register::H,
    5 => Register::L,
    6 => Register::M,
    7 => Register::A,
    _ => panic!("got invalid byte register"),
  }
}

#[cfg(test)]
mod tests {
  use parser::parser::Parser;

  use super::Interpreter;

  #[test]
  fn doesnt_panic() {
    let src = include_str!("../../test_files/even_numbers_in_array.asm");
    let mut int = Interpreter::new(Parser::from_source(src).parse().unwrap());

    int.assemble();

    int.env.set_memory_at(0x2040, 0x01);
    int.env.set_memory_at(0x2040, 0x01);
    int.env.set_memory_at(0x2041, 0x02);
    int.env.set_memory_at(0x2042, 0x03);
    int.env.set_memory_at(0x2043, 0x04);
    int.env.set_memory_at(0x2044, 0x0A);
    int.env.set_memory_at(0x2045, 0x05);
    int.env.set_memory_at(0x2046, 0x60);

    while int.execute().is_some() {}

    assert_eq!(int.env.memory_at(0x2070), Some(0x04));
  }
}
