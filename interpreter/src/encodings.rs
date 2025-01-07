//! Encodings for instruction mnemonics

// No operands
pub const NOP: u8 = 0x0;
pub const RAL: u8 = 0x17;
pub const RLC: u8 = 0x07;
pub const RRC: u8 = 0x0F;
pub const RAR: u8 = 0x1F;
pub const CMA: u8 = 0x2F;
pub const CMC: u8 = 0x3F;
pub const HLT: u8 = 0x7F;
pub const RNZ: u8 = 0xC0;
pub const RNC: u8 = 0xD0;
pub const RPO: u8 = 0xE0;
pub const RP: u8 = 0xF0;
pub const RZ: u8 = 0xC8;
pub const RC: u8 = 0xD8;
pub const RPE: u8 = 0xE8;
pub const RM: u8 = 0xF8;
pub const RET: u8 = 0xC9;
pub const SPHL: u8 = 0xF9;
pub const PCHL: u8 = 0xE9;
pub const XCHG: u8 = 0xEB;
pub const XTHL: u8 = 0xE3;
pub const STC: u8 = 0x37;
pub const DAA: u8 = 0x27;

// 1 operand
pub const ACI: u8 = 0xCE;
pub const SBI: u8 = 0xDE;
pub const XRI: u8 = 0xEE;
pub const CPI: u8 = 0xFE;

pub const ADD_B: u8 = 0x80;
pub const ADD_C: u8 = 0x81;
pub const ADD_D: u8 = 0x82;
pub const ADD_E: u8 = 0x83;
pub const ADD_H: u8 = 0x84;
pub const ADD_L: u8 = 0x85;
pub const ADD_M: u8 = 0x86;
pub const ADD_A: u8 = 0x87;

pub const ADC_B: u8 = 0x88;
pub const ADC_C: u8 = 0x89;
pub const ADC_D: u8 = 0x8A;
pub const ADC_E: u8 = 0x8B;
pub const ADC_H: u8 = 0x8C;
pub const ADC_L: u8 = 0x8D;
pub const ADC_M: u8 = 0x8E;
pub const ADC_A: u8 = 0x8F;

pub const SUB_B: u8 = 0x90;
pub const SUB_C: u8 = 0x91;
pub const SUB_D: u8 = 0x92;
pub const SUB_E: u8 = 0x93;
pub const SUB_H: u8 = 0x94;
pub const SUB_L: u8 = 0x95;
pub const SUB_M: u8 = 0x96;
pub const SUB_A: u8 = 0x97;

pub const SBB_B: u8 = 0x98;
pub const SBB_C: u8 = 0x99;
pub const SBB_D: u8 = 0x9A;
pub const SBB_E: u8 = 0x9B;
pub const SBB_H: u8 = 0x9C;
pub const SBB_L: u8 = 0x9D;
pub const SBB_M: u8 = 0x9E;
pub const SBB_A: u8 = 0x9F;

pub const ANA_B: u8 = 0xA0;
pub const ANA_C: u8 = 0xA1;
pub const ANA_D: u8 = 0xA2;
pub const ANA_E: u8 = 0xA3;
pub const ANA_H: u8 = 0xA4;
pub const ANA_L: u8 = 0xA5;
pub const ANA_M: u8 = 0xA6;
pub const ANA_A: u8 = 0xA7;

pub const XRA_B: u8 = 0xA8;
pub const XRA_C: u8 = 0xA9;
pub const XRA_D: u8 = 0xAA;
pub const XRA_E: u8 = 0xAB;
pub const XRA_H: u8 = 0xAC;
pub const XRA_L: u8 = 0xAD;
pub const XRA_M: u8 = 0xAE;
pub const XRA_A: u8 = 0xAF;

pub const ORA_B: u8 = 0xB0;
pub const ORA_C: u8 = 0xB1;
pub const ORA_D: u8 = 0xB2;
pub const ORA_E: u8 = 0xB3;
pub const ORA_H: u8 = 0xB4;
pub const ORA_L: u8 = 0xB5;
pub const ORA_M: u8 = 0xB6;
pub const ORA_A: u8 = 0xB7;

pub const CMP_B: u8 = 0xB8;
pub const CMP_C: u8 = 0xB9;
pub const CMP_D: u8 = 0xBA;
pub const CMP_E: u8 = 0xBB;
pub const CMP_H: u8 = 0xBC;
pub const CMP_L: u8 = 0xBD;
pub const CMP_M: u8 = 0xBE;
pub const CMP_A: u8 = 0xBF;

pub const INX_B: u8 = 0x03;
pub const INX_D: u8 = 0x13;
pub const INX_H: u8 = 0x23;
pub const INX_SP: u8 = 0x33;

pub const INR_B: u8 = 0x04;
pub const INR_D: u8 = 0x14;
pub const INR_H: u8 = 0x24;
pub const INR_M: u8 = 0x34;
pub const INR_C: u8 = 0x0C;
pub const INR_E: u8 = 0x1C;
pub const INR_L: u8 = 0x2C;
pub const INR_A: u8 = 0x3C;

pub const DCX_B: u8 = 0x0B;
pub const DCX_D: u8 = 0x1B;
pub const DCX_H: u8 = 0x2B;
pub const DCX_SP: u8 = 0x3B;

pub const DCR_B: u8 = 0x05;
pub const DCR_D: u8 = 0x15;
pub const DCR_H: u8 = 0x25;
pub const DCR_M: u8 = 0x35;
pub const DCR_C: u8 = 0x0D;
pub const DCR_E: u8 = 0x1D;
pub const DCR_L: u8 = 0x2D;
pub const DCR_A: u8 = 0x3D;

pub const DAD_B: u8 = 0x09;
pub const DAD_D: u8 = 0x19;
pub const DAD_H: u8 = 0x29;
pub const DAD_SP: u8 = 0x39;

pub const POP_B: u8 = 0xC1;
pub const POP_D: u8 = 0xD1;
pub const POP_H: u8 = 0xE1;
pub const POP_PSW: u8 = 0xF1;

pub const PUSH_B: u8 = 0xC5;
pub const PUSH_D: u8 = 0xD5;
pub const PUSH_H: u8 = 0xE5;
pub const PUSH_PSW: u8 = 0xF5;

pub const ADI: u8 = 0xC6;
pub const SUI: u8 = 0xD6;
pub const ANI: u8 = 0xE6;
pub const ORI: u8 = 0xF6;

pub const STA: u8 = 0x32;
pub const STAX_B: u8 = 0x02;
pub const STAX_D: u8 = 0x12;
pub const SHLD: u8 = 0x22;

pub const LDA: u8 = 0x3A;
pub const LDAX_B: u8 = 0x0A;
pub const LDAX_D: u8 = 0x1A;
pub const LHLD: u8 = 0x2A;

pub const RST_0: u8 = 0xC7;
pub const RST_2: u8 = 0xD7;
pub const RST_4: u8 = 0xE7;
pub const RST_6: u8 = 0xF7;
pub const RST_1: u8 = 0xCF;
pub const RST_3: u8 = 0xDF;
pub const RST_5: u8 = 0xEF;
pub const RST_7: u8 = 0xFF;

pub const JNZ: u8 = 0xC2;
pub const JNC: u8 = 0xD2;
pub const JPO: u8 = 0xE2;
pub const JP: u8 = 0xF2;
pub const JMP: u8 = 0xC3;
pub const JZ: u8 = 0xCA;
pub const JC: u8 = 0xDA;
pub const JPE: u8 = 0xEA;
pub const JM: u8 = 0xFA;
pub const CNZ: u8 = 0xC4;
pub const CNC: u8 = 0xD4;
pub const CPO: u8 = 0xE4;
pub const CP: u8 = 0xF4;
pub const CZ: u8 = 0xCC;
pub const CC: u8 = 0xDC;
pub const CPE: u8 = 0xEC;
pub const CM: u8 = 0xFC;
pub const CALL: u8 = 0xCD;

// 2 operands
pub const LXI_B: u8 = 0x01;
pub const LXI_D: u8 = 0x11;
pub const LXI_H: u8 = 0x21;
pub const LXI_SP: u8 = 0x31;

pub const MVI_B: u8 = 0x06;
pub const MVI_D: u8 = 0x16;
pub const MVI_H: u8 = 0x26;
pub const MVI_M: u8 = 0x36;
pub const MVI_C: u8 = 0x0E;
pub const MVI_E: u8 = 0x1E;
pub const MVI_L: u8 = 0x2E;
pub const MVI_A: u8 = 0x3E;

pub const MOV_B_B: u8 = 0x40;
pub const MOV_B_C: u8 = 0x41;
pub const MOV_B_D: u8 = 0x42;
pub const MOV_B_E: u8 = 0x43;
pub const MOV_B_H: u8 = 0x44;
pub const MOV_B_L: u8 = 0x45;
pub const MOV_B_M: u8 = 0x46;
pub const MOV_B_A: u8 = 0x47;

pub const MOV_C_B: u8 = 0x48;
pub const MOV_C_C: u8 = 0x49;
pub const MOV_C_D: u8 = 0x4A;
pub const MOV_C_E: u8 = 0x4B;
pub const MOV_C_H: u8 = 0x4C;
pub const MOV_C_L: u8 = 0x4D;
pub const MOV_C_M: u8 = 0x4E;
pub const MOV_C_A: u8 = 0x4F;

pub const MOV_D_B: u8 = 0x50;
pub const MOV_D_C: u8 = 0x51;
pub const MOV_D_D: u8 = 0x52;
pub const MOV_D_E: u8 = 0x53;
pub const MOV_D_H: u8 = 0x54;
pub const MOV_D_L: u8 = 0x55;
pub const MOV_D_M: u8 = 0x56;
pub const MOV_D_A: u8 = 0x57;

pub const MOV_E_B: u8 = 0x58;
pub const MOV_E_C: u8 = 0x59;
pub const MOV_E_D: u8 = 0x5A;
pub const MOV_E_E: u8 = 0x5B;
pub const MOV_E_H: u8 = 0x5C;
pub const MOV_E_L: u8 = 0x5D;
pub const MOV_E_M: u8 = 0x5E;
pub const MOV_E_A: u8 = 0x5F;

pub const MOV_H_B: u8 = 0x60;
pub const MOV_H_C: u8 = 0x61;
pub const MOV_H_D: u8 = 0x62;
pub const MOV_H_E: u8 = 0x63;
pub const MOV_H_H: u8 = 0x64;
pub const MOV_H_L: u8 = 0x65;
pub const MOV_H_M: u8 = 0x66;
pub const MOV_H_A: u8 = 0x67;

pub const MOV_L_B: u8 = 0x68;
pub const MOV_L_C: u8 = 0x69;
pub const MOV_L_D: u8 = 0x6A;
pub const MOV_L_E: u8 = 0x6B;
pub const MOV_L_H: u8 = 0x6C;
pub const MOV_L_L: u8 = 0x6D;
pub const MOV_L_M: u8 = 0x6E;
pub const MOV_L_A: u8 = 0x6F;

pub const MOV_M_B: u8 = 0x70;
pub const MOV_M_C: u8 = 0x71;
pub const MOV_M_D: u8 = 0x72;
pub const MOV_M_E: u8 = 0x73;
pub const MOV_M_H: u8 = 0x74;
pub const MOV_M_L: u8 = 0x75;
pub const MOV_M_A: u8 = 0x77;

pub const MOV_A_B: u8 = 0x78;
pub const MOV_A_C: u8 = 0x79;
pub const MOV_A_D: u8 = 0x7A;
pub const MOV_A_E: u8 = 0x7B;
pub const MOV_A_H: u8 = 0x7C;
pub const MOV_A_L: u8 = 0x7D;
pub const MOV_A_M: u8 = 0x7E;
pub const MOV_A_A: u8 = 0x7F;
