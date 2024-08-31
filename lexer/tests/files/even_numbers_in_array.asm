MVI C, 07H ; Array size
MVI B, 00H ; count number of even
LXI H, 2040H ; Array starting address
L1: MOV A, M
RAR
JC L2
INR B
L2: INX H
DCR C
JNZ L1
MOV A, B
STA 2070H
HLT