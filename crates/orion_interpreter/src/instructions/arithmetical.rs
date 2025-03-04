//! Arithmetical instructions
use crate::{
  encodings,
  registers::{self, RegisterPair},
  Environment,
};
use orion_lexer::{Flags, Register};

pub fn execute_add(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  // For ADD, the first 3 bits determine the register
  let register = registers::decode_register(instruction_byte & 0b111);
  let a = env.get_register_value(Register::A).unwrap();
  let r = env.get_register_value(register).unwrap();
  let res = a.wrapping_add(r);

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_adi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let res = a.wrapping_add(env.read_memory());

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_adc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte & 0b111);
  let a = env.get_register_value(Register::A).unwrap();
  let r = env.get_register_value(register).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a.wrapping_add(r).wrapping_add(carry_value);

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_aci(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a.wrapping_add(env.read_memory()).wrapping_add(carry_value);

  env.update_flags_arithmetic(a, res, true);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_sbb(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte & 0b111);
  let a = env.get_register_value(Register::A).unwrap();
  let r = env.get_register_value(register).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let res = a.wrapping_sub(r).wrapping_sub(carry_value);

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_sub(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let register = registers::decode_register(instruction_byte & 0b111);
  let a = env.get_register_value(Register::A).unwrap();
  let r = env.get_register_value(register).unwrap();
  let res = a.wrapping_sub(r);

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_sui(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let res = a.wrapping_sub(env.read_memory());

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_sbi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let res = a.wrapping_sub(env.read_memory());

  env.update_flags_arithmetic(a, res, false);

  env.registers.a = res;
  env.registers.next_pc();
}

pub fn execute_inr(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let old_carry = env.is_flag_set(Flags::Carry);

  let register = registers::decode_register((instruction_byte >> 3) & 0b111);
  let old_value = env.get_register_value(register).unwrap();
  let new_value = old_value.wrapping_add(1);

  env.set_register_value(register, new_value);

  env.update_flags_arithmetic(old_value, new_value, true);
  // `INR` preserves the carry flag
  env.set_flag(Flags::Carry, old_carry);

  env.registers.next_pc();
}

pub fn execute_inx(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == encodings::INX_B {
    let updated_value = env.read_register_pair(RegisterPair::BC).wrapping_add(1);

    env.write_register_pair(RegisterPair::BC, updated_value);
  } else if instruction_byte == encodings::INX_D {
    let updated_value = env.read_register_pair(RegisterPair::DE).wrapping_add(1);

    env.write_register_pair(RegisterPair::DE, updated_value);
  } else if instruction_byte == encodings::INX_H {
    let updated_value = env.read_register_pair(RegisterPair::HL).wrapping_add(1);

    env.write_register_pair(RegisterPair::HL, updated_value);
  } else if instruction_byte == encodings::INX_SP {
    env.registers.sp = env.registers.sp.wrapping_add(1);
  }

  env.registers.next_pc();
}

pub fn execute_dcr(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let carry = env.is_flag_set(Flags::Carry);

  let register = registers::decode_register((instruction_byte >> 3) & 0b111);
  let old_value = env.get_register_value(register).unwrap();
  let new_value = old_value.wrapping_sub(1);

  env.set_register_value(register, new_value);

  env.update_flags_arithmetic(old_value, new_value, false);
  // `DCR` preserves the carry flag
  env.set_flag(Flags::Carry, carry);

  env.registers.next_pc();
}

pub fn execute_dad(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let hl_value = env.read_register_pair(RegisterPair::HL);

  if instruction_byte == encodings::DAD_B {
    let bc_value = env.read_register_pair(RegisterPair::BC);
    let sum = bc_value.wrapping_add(hl_value);

    env.write_register_pair(RegisterPair::HL, sum);
    env.set_flag(Flags::Carry, sum < hl_value);
  } else if instruction_byte == encodings::DAD_D {
    let de_value = env.read_register_pair(RegisterPair::DE);
    let sum = de_value.wrapping_add(hl_value);

    env.write_register_pair(RegisterPair::HL, sum);
    env.set_flag(Flags::Carry, sum < hl_value);
  } else if instruction_byte == encodings::DAD_H {
    let sum = hl_value.wrapping_add(hl_value);

    env.write_register_pair(RegisterPair::HL, sum);
    env.set_flag(Flags::Carry, sum < hl_value);
  } else if instruction_byte == encodings::DAD_SP {
    let sum = env.registers.sp.wrapping_add(hl_value);

    env.write_register_pair(RegisterPair::HL, sum);
    env.set_flag(Flags::Carry, sum < hl_value);
  }

  env.registers.next_pc();
}

pub fn execute_daa(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let mut correction = 0;
  // Preserve the aux carry and carry flag, before doing the adjustment
  let mut is_aux_carry_set = env.is_flag_set(Flags::AuxiliaryCarry);
  let mut is_carry_set = env.is_flag_set(Flags::Carry);

  if (env.registers.a & 0xF) > 9 || is_aux_carry_set {
    // Add 6 to the lower nibble
    correction += 6;
    is_aux_carry_set = true;
  }

  if (env.registers.a >> 4) > 9 || is_carry_set {
    // Add 6 to the upper nibble
    correction += 6 << 4;
    is_carry_set = true
  }

  env.registers.a = env.registers.a.wrapping_add(correction);

  env.update_flags_logical(env.registers.a);
  // Update the carry flags to what they should be
  env.set_flag(Flags::AuxiliaryCarry, is_aux_carry_set);
  env.set_flag(Flags::Carry, is_carry_set);

  env.registers.next_pc();
}

pub fn execute_dcx(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == encodings::DCX_B {
    let updated_value = env.read_register_pair(RegisterPair::BC).wrapping_sub(1);

    env.write_register_pair(RegisterPair::BC, updated_value);
  } else if instruction_byte == encodings::DCX_D {
    let updated_value = env.read_register_pair(RegisterPair::DE).wrapping_sub(1);

    env.write_register_pair(RegisterPair::DE, updated_value);
  } else if instruction_byte == encodings::DCX_H {
    let updated_value = env.read_register_pair(RegisterPair::HL).wrapping_sub(1);

    env.write_register_pair(RegisterPair::HL, updated_value);
  } else if instruction_byte == encodings::DCX_SP {
    env.registers.sp = env.registers.sp.wrapping_sub(1);
  }

  env.registers.next_pc();
}

pub fn execute_rlc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let rotated = a.rotate_left(1);

  // Only the carry flag is updated
  env.set_flag(Flags::Carry, a >> 7 == 1);

  env.registers.a = rotated;
  env.registers.next_pc();
}

pub fn execute_rrc(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let rotated = a.rotate_right(1);

  // Only the carry flag is updated
  env.set_flag(Flags::Carry, a & 0x1 == 1);

  env.registers.a = rotated;
  env.registers.next_pc();
}

pub fn execute_rar(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
  let carry_value = env.is_flag_set(Flags::Carry) as u8;
  let rotated = (a >> 1) | (carry_value << 7);

  env.set_flag(Flags::Carry, a & 0x1 == 1);
  env.registers.a = rotated;
  env.registers.next_pc();
}

pub fn execute_ral(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let a = env.get_register_value(Register::A).unwrap();
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
