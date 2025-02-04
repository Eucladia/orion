//! Branching instructions
use crate::{registers, Environment};
use orion_lexer::{Flags, Register};

pub fn execute_cmp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  // The register is encoded in the lower 3 bits
  let register = registers::decode_register(instruction_byte & 0b111);
  let a = env.get_register_value(Register::A).unwrap();
  let r = env.get_register_value(register).unwrap();

  env.update_flags_arithmetic(a, a.wrapping_sub(r), false);

  env.registers.next_pc();
}

pub fn execute_cpi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let imm8 = env.read_memory();

  env.update_flags_arithmetic(a, a.wrapping_sub(imm8), false);

  env.registers.next_pc();
}

pub fn execute_rnz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Zero) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_rnc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Carry) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_rpo(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Parity) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_rp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Sign) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_rz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Zero) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_rc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Carry) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_rpe(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Parity) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_rm(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Sign) {
    let go_to = env.read_stack_u16();

    env.registers.pc = go_to;
  } else {
    env.registers.next_pc();
  }
}

pub fn execute_ret(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let go_to = env.read_stack_u16();

  env.registers.pc = go_to;
}

pub fn execute_call(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  env.write_stack_u16(ret_to);
  env.registers.pc = jump_to;
}

pub fn execute_cm(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if env.is_flag_set(Flags::Sign) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_cpe(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if env.is_flag_set(Flags::Parity) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_cc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if env.is_flag_set(Flags::Carry) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_cz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if env.is_flag_set(Flags::Zero) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_cp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if !env.is_flag_set(Flags::Sign) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_cpo(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if !env.is_flag_set(Flags::Parity) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_cnc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if !env.is_flag_set(Flags::Carry) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_cnz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();
  let ret_to = env.registers.next_pc();

  if !env.is_flag_set(Flags::Zero) {
    env.write_stack_u16(ret_to);
    env.registers.pc = jump_to;
  }
}

pub fn execute_jm(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if env.is_flag_set(Flags::Sign) {
    env.registers.pc = jump_to;
  }
}

pub fn execute_jpe(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if env.is_flag_set(Flags::Parity) {
    env.registers.pc = jump_to;
  }
}

pub fn execute_jc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if env.is_flag_set(Flags::Carry) {
    env.registers.pc = jump_to;
  }
}

pub fn execute_jz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if env.is_flag_set(Flags::Zero) {
    env.registers.pc = jump_to;
  }
}

pub fn execute_jmp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.pc = jump_to;
}

pub fn execute_jp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if !env.is_flag_set(Flags::Sign) {
    env.registers.pc = jump_to;
  }
}

pub fn execute_jpo(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if !env.is_flag_set(Flags::Parity) {
    env.registers.pc = jump_to;
  }
}

pub fn execute_jnc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if !env.is_flag_set(Flags::Carry) {
    env.registers.pc = jump_to;
  }
}

pub fn execute_jnz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let jump_to = env.read_memory_u16();

  env.registers.next_pc();

  if !env.is_flag_set(Flags::Zero) {
    env.registers.pc = jump_to;
  }
}
