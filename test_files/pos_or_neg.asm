; Stores 0 in 0x2055 if the number is positive, and 1 if negative
LDA 2050H
RAL
JC L1
MVI A, 00H
STA 2055H
JMP DONE
L1: MVI A, 01H
STA 2055H
DONE: HLT