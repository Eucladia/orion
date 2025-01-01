//! Manipulation related instructions
use crate::Environment;
use lexer::Flags;

pub fn execute_push(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0xC5 {
    env.write_stack_u8(env.registers.b);
    env.write_stack_u8(env.registers.c);
  } else if instruction_byte == 0xD5 {
    env.write_stack_u8(env.registers.d);
    env.write_stack_u8(env.registers.e);
  } else if instruction_byte == 0xE5 {
    env.write_stack_u8(env.registers.h);
    env.write_stack_u8(env.registers.l);
  } else if instruction_byte == 0xF5 {
    env.write_stack_u8(env.registers.a);
    env.write_stack_u8(env.flags);
  }

  env.registers.next_pc();
}

pub fn execute_pop(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let lower = env.read_stack_u8();
  let upper = env.read_stack_u8();

  if instruction_byte == 0xC1 {
    env.registers.b = upper;
    env.registers.c = lower;
  } else if instruction_byte == 0xD1 {
    env.registers.d = upper;
    env.registers.e = lower;
  } else if instruction_byte == 0xE1 {
    env.registers.h = upper;
    env.registers.l = lower;
  } else if instruction_byte == 0xF1 {
    env.registers.a = upper;
    env.flags = lower;
  }

  env.registers.next_pc();
}

pub fn execute_stc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.set_flag(Flags::Carry, true);

  env.registers.next_pc();
}

pub fn execute_rst(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  // The restart number is stored in bits 3-5
  let rst_number = (instruction_byte >> 3) & 0x7;
  let target_address = (rst_number as u16) * 8;

  // Push the next instruction onto the stack
  env.write_stack_address(env.registers.pc.wrapping_add(1));

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
