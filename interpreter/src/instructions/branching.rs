//! Branching instructions
use crate::{registers, Environment};
use lexer::{Flags, Register};

pub fn execute_cmp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0xB8);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();

  env.update_flags_arithmetic(a, a.wrapping_sub(r), false);

  env.registers.pc += 1;
}

pub fn execute_cpi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();

  env.update_flags_arithmetic(a, a.wrapping_sub(imm8), false);

  env.registers.pc += 2;
}

pub fn execute_rnz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Zero) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_rnc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Carry) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_rpo(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Parity) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_rp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if !env.is_flag_set(Flags::Sign) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_rz(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Zero) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_rc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Carry) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_rpe(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Parity) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_rm(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if env.is_flag_set(Flags::Sign) {
    let go_to = env.return_from_call().unwrap();

    env.registers.pc = go_to;
  } else {
    env.registers.pc += 1;
  }
}

pub fn execute_ret(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let go_to = env.return_from_call().unwrap();

  env.registers.pc = go_to;
}

pub fn execute_call(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
  let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
  let jump_to = (label_upper as u16) << 8 | label_lower as u16;

  env.add_to_call_stack(env.registers.pc + 3);
  env.registers.pc = jump_to;
}

pub fn execute_cm(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_cpe(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_cc(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_cz(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_cp(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_cpo(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_cnc(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_cnz(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jm(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jpe(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jc(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jz(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jmp(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let label_lower = env.memory_at(env.registers.pc + 1).unwrap();
  let label_upper = env.memory_at(env.registers.pc + 2).unwrap();
  let jump_to = (label_upper as u16) << 8 | label_lower as u16;

  env.registers.pc = jump_to;
}

pub fn execute_jp(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jpo(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jnc(env: &mut Environment, instruction_byte: u8) {
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

pub fn execute_jnz(env: &mut Environment, instruction_byte: u8) {
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
