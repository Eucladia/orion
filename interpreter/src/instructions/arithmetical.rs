//! Arithmetical instructions
use crate::{registers, Environment};
use lexer::{Flags, Register};

pub fn execute_add(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0x80);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a.wrapping_add(r);

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_adi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let res = a.wrapping_add(env.read_memory());

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_adc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0x88);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a.wrapping_add(r).wrapping_add(carry_value);

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_aci(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a.wrapping_add(env.read_memory()).wrapping_add(carry_value);

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_sbb(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0x98);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a.wrapping_sub(r).wrapping_sub(carry_value);

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_sub(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte - 0x90);
  let a = registers::get_register_value(env, Register::A).unwrap();
  let r = registers::get_register_value(env, register).unwrap();
  let res = a.wrapping_sub(r);

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}
pub fn execute_sui(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let res = a.wrapping_sub(env.read_memory());

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}
pub fn execute_sbi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let res = a.wrapping_sub(env.read_memory());

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_inr(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let carry = env.is_flag_set(Flags::Carry);

  if instruction_byte == 0x04 {
    let old_value = env.registers.b;

    env.registers.b = old_value.wrapping_add(1);
    env.update_flags_arithmetic(old_value, env.registers.b, true);
  } else if instruction_byte == 0x14 {
    let old_value = env.registers.d;

    env.registers.d = old_value.wrapping_add(1);
    env.update_flags_arithmetic(old_value, env.registers.d, true);
  } else if instruction_byte == 0x24 {
    let old_value = env.registers.h;

    env.registers.h = old_value.wrapping_add(1);
    env.update_flags_arithmetic(old_value, env.registers.h, true);
  } else if instruction_byte == 0x34 {
    let address = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let value = env.memory_at(address);
    let new_value = value.wrapping_add(1);

    env.write_memory(address, new_value);
    env.update_flags_arithmetic(value, new_value, true);
  } else if instruction_byte == 0x0C {
    let old_value = env.registers.c;

    env.registers.c = old_value.wrapping_add(1);
    env.update_flags_arithmetic(old_value, env.registers.c, true);
  } else if instruction_byte == 0x1C {
    let old_value = env.registers.e;

    env.registers.e = old_value.wrapping_add(1);
    env.update_flags_arithmetic(old_value, env.registers.e, true);
  } else if instruction_byte == 0x2C {
    let old_value = env.registers.l;

    env.registers.l = old_value.wrapping_add(1);
    env.update_flags_arithmetic(old_value, env.registers.l, true);
  } else if instruction_byte == 0x3C {
    let old_value = env.registers.a;

    env.registers.a = old_value.wrapping_add(1);
    env.update_flags_arithmetic(old_value, env.registers.a, true);
  }

  // INR preserves the carry flag
  env.set_flag(Flags::Carry, carry);
  env.registers.next_pc();
}

pub fn execute_inx(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x03 {
    let curr_value = (env.registers.b as u16) << 8 | env.registers.c as u16;
    let updated_value = curr_value.wrapping_add(1);

    env.registers.b = (updated_value >> 8) as u8;
    env.registers.c = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x13 {
    let curr_value = (env.registers.d as u16) << 8 | env.registers.e as u16;
    let updated_value = curr_value.wrapping_add(1);

    env.registers.d = (updated_value >> 8) as u8;
    env.registers.e = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x23 {
    let curr_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let updated_value = curr_value.wrapping_add(1);

    env.registers.h = (updated_value >> 8) as u8;
    env.registers.l = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x33 {
    env.registers.sp = env.registers.sp.wrapping_add(1);
  }

  env.registers.next_pc();
}

pub fn execute_dcr(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let carry = env.is_flag_set(Flags::Carry);

  if instruction_byte == 0x05 {
    let old_value = env.registers.b;

    env.registers.b = old_value.wrapping_sub(1);
    env.update_flags_arithmetic(old_value, env.registers.b, false);
  } else if instruction_byte == 0x15 {
    let old_value = env.registers.d;

    env.registers.d = old_value.wrapping_sub(1);
    env.update_flags_arithmetic(old_value, env.registers.d, false);
  } else if instruction_byte == 0x25 {
    let old_value = env.registers.h;

    env.registers.h = old_value.wrapping_sub(1);
    env.update_flags_arithmetic(old_value, env.registers.h, false);
  } else if instruction_byte == 0x35 {
    let address = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let value = env.memory_at(address);
    let new_value = value.wrapping_sub(1);

    env.write_memory(address, new_value);
    env.update_flags_arithmetic(value, new_value, false);
  } else if instruction_byte == 0x0D {
    let old_value = env.registers.c;

    env.registers.c = old_value.wrapping_sub(1);
    env.update_flags_arithmetic(old_value, env.registers.c, false);
  } else if instruction_byte == 0x1D {
    let old_value = env.registers.e;

    env.registers.e = old_value.wrapping_sub(1);
    env.update_flags_arithmetic(old_value, env.registers.e, false);
  } else if instruction_byte == 0x2D {
    let old_value = env.registers.l;

    env.registers.l = old_value.wrapping_sub(1);
    env.update_flags_arithmetic(old_value, env.registers.l, false);
  } else if instruction_byte == 0x3D {
    let old_value = env.registers.a;

    env.registers.a = old_value.wrapping_sub(1);
    env.update_flags_arithmetic(old_value, env.registers.a, false);
  }

  // DCR preserves the carry flag
  env.set_flag(Flags::Carry, carry);
  env.registers.next_pc();
}

pub fn execute_dad(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x09 {
    let bc_value = (env.registers.b as u16) << 8 | env.registers.c as u16;
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = bc_value.wrapping_add(hl_value);

    env.set_flag(Flags::Carry, sum < hl_value);
    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  } else if instruction_byte == 0x19 {
    let de_value = (env.registers.d as u16) << 8 | env.registers.e as u16;
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = de_value.wrapping_add(hl_value);

    env.set_flag(Flags::Carry, sum < hl_value);
    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  } else if instruction_byte == 0x29 {
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = hl_value.wrapping_add(hl_value);

    env.set_flag(Flags::Carry, sum < hl_value);
    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  } else if instruction_byte == 0x39 {
    let hl_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let sum = env.registers.sp.wrapping_add(hl_value);

    env.set_flag(Flags::Carry, sum < hl_value);
    env.registers.h = (sum >> 8) as u8;
    env.registers.l = (sum & 0xFF) as u8;
  }

  env.registers.next_pc();
}

pub fn execute_daa(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let acc = env.registers.a;
  let mut correction = 0;

  if (acc & 0xF) > 9 || env.is_flag_set(Flags::AuxiliaryCarry) {
    // Add 6 to the lower nibble
    correction += 6;
    env.set_flag(Flags::AuxiliaryCarry, true);
  }

  if (acc >> 4) > 9 || env.is_flag_set(Flags::Carry) {
    // Add 6 to the upper nibble
    correction += 6 << 4;
    env.set_flag(Flags::Carry, true);
  }

  let res = acc.wrapping_add(correction);

  env.registers.a = res;

  env.set_flag(Flags::Zero, res == 0);
  env.set_flag(Flags::Sign, res & 0x80 != 0);
  env.set_flag(Flags::Parity, res.count_ones() % 2 == 0);

  env.registers.pc += 1;
}

pub fn execute_dcx(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x0B {
    let curr_value = (env.registers.b as u16) << 8 | env.registers.c as u16;
    let updated_value = curr_value.wrapping_sub(1);

    env.registers.b = (updated_value >> 8) as u8;
    env.registers.c = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x1B {
    let curr_value = (env.registers.d as u16) << 8 | env.registers.e as u16;
    let updated_value = curr_value.wrapping_sub(1);

    env.registers.d = (updated_value >> 8) as u8;
    env.registers.e = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x2B {
    let curr_value = (env.registers.h as u16) << 8 | env.registers.l as u16;
    let updated_value = curr_value.wrapping_sub(1);

    env.registers.h = (updated_value >> 8) as u8;
    env.registers.l = (updated_value & 0xFF) as u8;
  } else if instruction_byte == 0x3B {
    let updated_value = env.registers.sp.wrapping_sub(1);

    env.registers.b = (updated_value >> 8) as u8;
    env.registers.c = (updated_value & 0xFF) as u8;
  }

  env.registers.next_pc();
}

pub fn execute_rlc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let rotated = a.rotate_left(1);

  // Only the carry flag is updated
  env.set_flag(Flags::Carry, a >> 7 == 1);

  env.registers.a = rotated;
  env.registers.next_pc();
}

pub fn execute_rrc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let rotated = a.rotate_right(1);

  // Only the carry flag is updated
  env.set_flag(Flags::Carry, a & 0x1 == 1);

  env.registers.a = rotated;
  env.registers.next_pc();
}

pub fn execute_rar(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let rotated = (a >> 1) | (carry_value << 7);

  env.set_flag(Flags::Carry, a & 0x1 == 1);
  env.registers.a = rotated;
  env.registers.next_pc();
}

pub fn execute_ral(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = registers::get_register_value(env, Register::A).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let rotated = (a << 1) | carry_value;

  env.set_flag(Flags::Carry, a >> 7 == 1);
  env.registers.a = rotated;
  env.registers.next_pc();
}

pub fn execute_cma(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;
  env.registers.a = !env.registers.a;

  env.registers.next_pc();
}

pub fn execute_cmc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.set_flag(Flags::Carry, !env.is_flag_set(Flags::Carry));

  env.registers.next_pc();
}
