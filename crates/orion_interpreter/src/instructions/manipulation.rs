//! Manipulation related instructions
use crate::{encodings, registers::RegisterPair, Environment};
use orion_lexer::Flags;

pub fn execute_push(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  if instruction_byte == encodings::PUSH_B {
    env.write_stack_u16(env.read_register_pair(RegisterPair::BC));
  } else if instruction_byte == encodings::PUSH_D {
    env.write_stack_u16(env.read_register_pair(RegisterPair::DE));
  } else if instruction_byte == encodings::PUSH_H {
    env.write_stack_u16(env.read_register_pair(RegisterPair::HL));
  } else if instruction_byte == encodings::PUSH_PSW {
    env.write_stack_u16(env.read_register_pair(RegisterPair::PSW));
  }

  env.registers.next_pc();
}

pub fn execute_pop(env: &mut Environment, instruction_byte: u8) {
  env.registers.ir = instruction_byte;

  let data = env.read_stack_u16();

  if instruction_byte == encodings::POP_B {
    env.write_register_pair(RegisterPair::BC, data);
  } else if instruction_byte == encodings::POP_D {
    env.write_register_pair(RegisterPair::DE, data);
  } else if instruction_byte == encodings::POP_H {
    env.write_register_pair(RegisterPair::HL, data);
  } else if instruction_byte == encodings::POP_PSW {
    env.write_register_pair(RegisterPair::PSW, data);
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

  // The restart number is stored in bits 345
  let rst_number = (instruction_byte >> 3) & 0b111;
  let target_address = (rst_number as u16) * 8;

  // Push the next instruction onto the stack
  env.write_stack_u16(env.registers.pc.wrapping_add(1));

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
