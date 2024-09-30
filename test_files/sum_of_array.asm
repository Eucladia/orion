MVI C, 05H ; counter
LXI H, 2050H
MOV A, M
MVI B, 00H ; to store carry
L0: INX H
ADD M
JNC L1
INR B ; if carry, increment B
L1: DCR C
JNZ L0
STA 3000H
MOV A, B
STA 3001H
HLT