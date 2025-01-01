//! Manipulation related instructions
use crate::Environment;
use lexer::Flags;

pub fn execute_push(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0xC5 {
    env.registers.dr = (env.registers.c as u16) << 8 | env.registers.b as u16;

    env.set_memory_at(env.registers.sp, env.registers.b);
    env.set_memory_at(env.registers.sp.wrapping_sub(1), env.registers.c);
  } else if instruction_byte == 0xD5 {
    env.registers.dr = (env.registers.e as u16) << 8 | env.registers.d as u16;

    env.set_memory_at(env.registers.sp, env.registers.d);
    env.set_memory_at(env.registers.sp.wrapping_sub(1), env.registers.e);
  } else if instruction_byte == 0xE5 {
    env.registers.dr = (env.registers.l as u16) << 8 | env.registers.h as u16;

    env.set_memory_at(env.registers.sp, env.registers.h);
    env.set_memory_at(env.registers.sp.wrapping_sub(1), env.registers.l);
  } else if instruction_byte == 0xF5 {
    env.registers.dr = (env.flags as u16) << 8 | env.registers.a as u16;

    env.set_memory_at(env.registers.sp, env.registers.a);
    env.set_memory_at(env.registers.sp.wrapping_sub(1), env.flags);
  }

  env.registers.sp = env.registers.sp.wrapping_sub(2);
  env.registers.next_pc();
}

pub fn execute_pop(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let lower = env.memory_at(env.registers.sp.wrapping_add(1)).unwrap();
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

  env.registers.sp = env.registers.sp.wrapping_add(2);
  env.registers.next_pc();
}

pub fn execute_stc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.set_flag(Flags::Carry, true);

  env.registers.pc = env.registers.pc.wrapping_add(1);
}

pub fn execute_rst(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  // The restart number is stored in bits 3-5
  let rst_number = (instruction_byte >> 3) & 0x7;
  let target_address = (rst_number as u16) * 8;

  // Push the next instruction onto the stack
  let pc = env.registers.pc.wrapping_add(1);

  env.set_memory_at(env.registers.sp, (pc >> 8) as u8);
  env.set_memory_at(env.registers.sp.wrapping_sub(1), (pc & 0xFF) as u8);

  env.registers.sp = env.registers.sp.wrapping_sub(1);
  env.registers.pc = target_address;
}

pub fn execute_hlt(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;
  env.registers.next_pc();
}

pub fn execute_nop(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;
  env.registers.next_pc();
}
