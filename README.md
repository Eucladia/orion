<div align="center">
  <h1><code>Orion</code></h1>

  <p><b>An <a href="https://en.wikipedia.org/wiki/Intel_8085">Intel 8085</a> simulator.</b></p>

  <strong>⚠️ Orion is still in development, there may be bugs! 🐛</strong>
</div>

## Supported Features
### Types
- `reg` is any one of the registers `A`, `B`, `C`, `D`, `E`, `H`, `L`, or `M` (memory at register pair HL).
- `rp` is a register pair, these include registers `B`, `D`, and `H`. Some instructions may accept `SP` or `PSW` as a register pair.
- `d16` is either a 2 byte string literal, 16-bit number, a label, or an expression.
- `a16` is either a 16 bit number, a label, or an expression.
- `d8` is either a 1 byte string literal, 8-bit number, an 8-bit label, or an expression.

### Instructions
`LXI <rp or SP>, <d16>` - Loads the 16-bit data into the register pair.

`STAX <rp>`             - Stores the accumulator at the memory location specified by the register pair (B or D).

`LDAX <rp>`             - Loads the accumulator from the memory location specified by the register pair (B or D).

`STA <a16>`             - Stores the accumulator at the specified memory address.

`LDA <a16>`             - Loads the accumulator from the specified memory address.

`SHLD <a16>`            - Stores the contents of register pair HL at the specified memory address.

`LHLD <a16>`            - Loads the contents of register pair HL from the specified memory address.

`MOV <reg>, <reg>`      - Copies data from the second register to the first register.

`MVI <reg>, <d8>`       - Loads the 8-bit immediate data into the destination register.

`LXI <rp>, <d16>`       - Loads a 16-bit immediate value into the register pair.

`INR <reg>`             - Increments the specified register by 1.

`DCR <reg>`             - Decrements the specified register by 1.

`INX <rp>`              - Increments the specified register pair by 1.

`DCX <rp>`              - Decrements the specified register pair by 1.

`DAD <rp>`              - Adds the specified register pair to HL.

`ADD <reg>`             - Adds the value of the source register to the accumulator.

`ADC <reg>`             - Adds the value of the source register to the accumulator with carry.

`SUB <reg>`             - Subtracts the value of the source register from the accumulator.

`SBB <reg>`             - Subtracts the value of the source register from the accumulator with borrow.

`ANA <reg>`             - Performs a bitwise AND between the accumulator and the source register.

`XRA <reg>`             - Performs a bitwise XOR between the accumulator and the source register.

`ORA <reg>`             - Performs a bitwise OR between the accumulator and the source register.

`CMP <reg>`             - Compares the accumulator with the source register.

`CPI <d8>`              - Compares the accumulator with an immediate 8-bit value.

`RLC`                   - Rotates the accumulator left through the carry.

`RRC`                   - Rotates the accumulator right through the carry.

`RAL`                   - Rotates the accumulator left through the carry flag.

`RAR`                   - Rotates the accumulator right through the carry flag.

`CMA`                   - Complements the accumulator.

`CMC`                   - Complements the carry flag.

`STC`                   - Sets the carry flag.

`PUSH <rp>`             - Pushes the contents of the register pair onto the stack.

`POP <rp>`              - Pops the top two bytes from the stack into the register pair.

`XCHG`                  - Exchanges the contents of register pair HL with DE.

`XTHL`                  - Swaps HL with the top of the stack.

`SPHL`                  - Copies the contents of HL into SP.

`JMP <a16>`             - Jumps to the specified memory address.

`JC <a16>`              - Jumps to the specified memory address if the carry flag is set.

`JNC <a16>`             - Jumps to the specified memory address if the carry flag is not set.

`JZ <a16>`              - Jumps to the specified memory address if the zero flag is set.

`JNZ <a16>`             - Jumps to the specified memory address if the zero flag is not set.

`JP <a16>`              - Jumps to the specified memory address if the sign flag is not set (positive).

`JM <a16>`              - Jumps to the specified memory address if the sign flag is set (negative).

`CALL <a16>`            - Calls the subroutine at the specified address.

`CC <a16>`              - Calls the subroutine at the specified address if the carry flag is set.

`CNC <a16>`             - Calls the subroutine at the specified address if the carry flag is not set.

`CZ <a16>`              - Calls the subroutine at the specified address if the zero flag is set.

`CNZ <a16>`             - Calls the subroutine at the specified address if the zero flag is not set.

`CP <a16>`              - Calls the subroutine at the specified address if the sign flag is not set (positive).

`CM <a16>`              - Calls the subroutine at the specified address if the sign flag is set (negative).

`RET`                   - Returns from a subroutine.

`RC`                    - Returns from a subroutine if the carry flag is set.

`RNC`                   - Returns from a subroutine if the carry flag is not set.

`RZ`                    - Returns from a subroutine if the zero flag is set.

`RNZ`                   - Returns from a subroutine if the zero flag is not set.

`RP`                    - Returns from a subroutine if the sign flag is not set (positive).

`RM`                    - Returns from a subroutine if the sign flag is set (negative).

`NOP`                   - Does nothing.

`HLT`                   - Halts execution.


### Unsupported Instructions
`IN <d8>`  - Reads a byte from the specified input port.

`OUT <d8>` - Writes the accumulator to the specified output port.

`EI`       - Enables interrupts.

`DI`       - Disables interrupts.

### Directives
`<IDENTIFIER> EQU <d16>` - Assigns the 16-bit value to that identifier.

`<IDENTIFIER> SET <d16>` - Assigns the 16-bit value to that identifier, allowing redeclaration.

`DB <...d8>`             - Writes up to 8 8-bit values at the current location counter.

`DW <...d16>`            - Writes up to 8 16-bit values at the current location counter.

`DS <d16>`               - Reserves the specified amount of storage.

`ORG <d16>`              - Changes the location counter.

`END`                    - Stop assembling.

## References
- https://www.lehigh.edu/~mdw0/ece33/8085-codes.pdf
- https://www.inf.pucrs.br/~calazans/undergrad/orgcomp_EC/mat_microproc/intel-8085_datasheet.pdf
- https://bitsavers.org/components/intel/MCS80/9800301D_8080_8085_Assembly_Language_Programming_Manual_May81.pdf
