//! Logical instructions
use crate::{registers, Environment};
use lexer::{Flags, Register};

// The first three bits are the register for these instructions
pub fn execute_ora(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte & 0b111);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a | r;

  env.update_flags_logical(res);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_ori(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let res = a | env.read_memory();

  env.update_flags_logical(res);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_ana(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte & 0b111);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a & r;

  env.update_flags_logical(res);

  // On 8058, AND always sets the AC flag
  env.set_flag(Flags::AuxiliaryCarry, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_ani(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let res = a & env.read_memory();

  env.update_flags_logical(res);

  // On 8058, AND always sets the AC flag
  env.set_flag(Flags::AuxiliaryCarry, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_xri(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let res = a ^ env.read_memory();

  env.update_flags_logical(res);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_xra(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte & 0b111);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a ^ r;

  env.update_flags_logical(res);

  env.registers.a = res;
  env.registers.next_pc();
}
