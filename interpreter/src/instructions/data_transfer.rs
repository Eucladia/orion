//! Data transfer instructions
use crate::{registers, Environment};
use lexer::Register;

pub fn execute_mov(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let (dest, src) = if instruction_byte == 0x77 {
    (Register::M, Register::A)
  } else {
    let base = instruction_byte - 0x40;

    (
      registers::decode_register(base / 8),
      registers::decode_register(base % 8),
    )
  };

  let reg_value = registers::get_register_value(env, src).unwrap();

  registers::set_register_value(env, dest, reg_value);

  env.registers.pc = env.registers.pc.wrapping_add(1);
}

pub fn execute_mvi(env: &mut Environment, b: u8) {
  env.registers.ir = b;

  let dest = match b {
    0x06 => Register::B,
    0x16 => Register::D,
    0x26 => Register::H,
    0x36 => Register::M,

    0x0E => Register::C,
    0x1E => Register::E,
    0x2E => Register::L,
    0x3E => Register::A,
    _ => unreachable!(),
  };

  let value = env.read_memory();

  registers::set_register_value(env, dest, value);

  env.registers.next_pc();
}

pub fn execute_lxi(env: &mut Environment, byte: u8) {
  env.registers.ir = byte;

  let lower = env.read_memory();
  let upper = env.read_memory();

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
    // Stack pointer
    0x31 => {
      env.registers.sp = ((upper as u16) << 8) | lower as u16;
    }
    _ => unreachable!(),
  }

  env.registers.next_pc();
}

pub fn execute_ldax(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == 0x0A {
    let address = (env.registers.b as u16) << 8 | env.registers.c as u16;

    env.registers.a = env.memory_at(address);
  } else if instruction_byte == 0x1A {
    let address = (env.registers.d as u16) << 8 | env.registers.e as u16;

    env.registers.a = env.memory_at(address);
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

  if instruction_byte == 0x02 {
    let address = (env.registers.b as u16) << 8 | env.registers.c as u16;

    env.write_memory(address, env.registers.a);
  } else if instruction_byte == 0x12 {
    let address = (env.registers.d as u16) << 8 | env.registers.e as u16;

    env.write_memory(address, env.registers.a);
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

  env.registers.h = env.read_memory();
  env.registers.l = env.read_memory();

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

  env.registers.sp = ((env.registers.h as u16) << 8) | (env.registers.l as u16);

  env.registers.next_pc();
}

pub fn execute_pchl(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  env.registers.pc = ((env.registers.h as u16) << 8) | (env.registers.l as u16);
}
