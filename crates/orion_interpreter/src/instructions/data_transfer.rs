//! Data transfer instructions
use crate::{
  encodings,
  registers::{self, RegisterPair},
  Environment,
};

pub fn execute_mov(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  // The first 6 bits determine the destination and source registers in MOV
  let dest = registers::decode_register((instruction_byte >> 3) & 0b111);
  let src = registers::decode_register(instruction_byte & 0b111);
  let src_value = env.get_register_value(src).unwrap();

  env.set_register_value(dest, src_value);

  env.registers.next_pc();
}

pub fn execute_mvi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  // The destination register is stored in bits 345 in MVI
  let dest = registers::decode_register((instruction_byte >> 3) & 0b111);
  let value = env.read_memory();

  env.set_register_value(dest, value);

  env.registers.next_pc();
}

pub fn execute_lxi(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let data = env.read_memory_u16();

  if instruction_byte == encodings::LXI_B {
    env.write_register_pair(RegisterPair::BC, data);
  } else if instruction_byte == encodings::LXI_D {
    env.write_register_pair(RegisterPair::DE, data);
  } else if instruction_byte == encodings::LXI_H {
    env.write_register_pair(RegisterPair::HL, data);
  } else if instruction_byte == encodings::LXI_SP {
    env.write_register_pair(RegisterPair::SP, data);
  }

  env.registers.next_pc();
}

pub fn execute_ldax(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == encodings::LDAX_B {
    env.registers.a = env.memory_at(env.read_register_pair(RegisterPair::BC));
  } else if instruction_byte == encodings::LDAX_D {
    env.registers.a = env.memory_at(env.read_register_pair(RegisterPair::DE));
  }

  env.registers.next_pc();
}

pub fn execute_lda(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let addr = env.read_memory_u16();
  let value = env.memory_at(addr);

  env.registers.a = value;
  env.registers.next_pc();
}

pub fn execute_stax(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == encodings::STAX_B {
    env.write_memory(env.read_register_pair(RegisterPair::BC), env.registers.a);
  } else if instruction_byte == encodings::STAX_D {
    env.write_memory(env.read_register_pair(RegisterPair::DE), env.registers.a);
  }

  env.registers.next_pc();
}

pub fn execute_sta(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let addr = env.read_memory_u16();

  env.write_memory(addr, env.registers.a);

  env.registers.next_pc();
}

pub fn execute_shld(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let addr = env.read_memory_u16();

  // SHLD sets in inverse order
  env.write_memory(addr, env.registers.l);
  env.write_memory(addr + 1, env.registers.h);

  env.registers.next_pc();
}

pub fn execute_lhld(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.registers.l = env.read_memory();
  env.registers.h = env.read_memory();

  env.registers.next_pc();
}

pub fn execute_xchg(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  std::mem::swap(&mut env.registers.h, &mut env.registers.d);
  std::mem::swap(&mut env.registers.l, &mut env.registers.e);

  env.registers.next_pc();
}

pub fn execute_xthl(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  std::mem::swap(&mut env.memory_at(env.registers.sp), &mut env.registers.l);
  std::mem::swap(
    &mut env.memory_at(env.registers.sp.wrapping_add(1)),
    &mut env.registers.h,
  );

  env.registers.next_pc();
}

pub fn execute_sphl(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.registers.sp = env.read_register_pair(RegisterPair::HL);

  env.registers.next_pc();
}

pub fn execute_pchl(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.registers.pc = env.read_register_pair(RegisterPair::HL);
}
