//! Logical instructions
use crate::{registers, Environment};
use lexer::{Flags, Register};

pub fn execute_ora(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0xB0);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a | r;

  env.update_flags_u8_arithmetic(a, a | r, false);

  // These are reset
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 1;
}

pub fn execute_xra(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0xA8);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a ^ r;

  env.update_flags_u8_arithmetic(a, a ^ r, false);
  // These flags get reset
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 1;
}

pub fn execute_ana(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0xA0);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a & r;

  env.update_flags_u8_arithmetic(a, a & r, false);
  // Aux carry is always set when doing a logical AND on 8085
  env.set_flag(Flags::AuxiliaryCarry, true);
  // Carry is always reset
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 1;
}

pub fn execute_ori(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a | imm8;

  env.update_flags_u8_arithmetic(a, res, false);

  // ORI resets the aux carry and carry flags
  env.set_flag(Flags::AuxiliaryCarry, false);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 2;
}

pub fn execute_ani(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a & imm8;

  env.update_flags_u8_arithmetic(a, res, false);
  // Aux carry is always set on 8085, see page 1-12 on bitsavers 8080/8085 manual
  env.set_flag(Flags::AuxiliaryCarry, true);
  env.set_flag(Flags::Carry, false);

  env.registers.a = res;
  env.registers.pc += 2;
}

pub fn execute_xri(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let imm8 = env.memory_at(env.registers.pc + 1).unwrap();
  let res = a ^ imm8;

  env.update_flags_u8_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.pc += 2;
}
