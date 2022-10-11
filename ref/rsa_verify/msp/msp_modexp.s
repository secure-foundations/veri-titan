.globl mod_pow
mod_pow:
  PUSHM.W	#7,R10
  MOV.W	R12,R10
  MOV.W	R13,R9
  MOV.W	R13,R8
  ADD.W	#384,R8
  MOV.W	R15,R7
  MOV.W	#8,R6
  MOV.W	#0,R5
  MOV.W	R9,R12
  MOV.W	R14,R13
  MOV.W	R7,R14
  CALL #mont_mul

w_start0:
	CMP.W	R6,R5
	JGE	w_end0
  MOV.W	R8,R12
  MOV.W	R9,R13
  MOV.W	R9,R14
  CALL #mont_mul
  MOV.W	R9,R12
  MOV.W	R8,R13
  MOV.W	R8,R14
  CALL #mont_mul
  ADD.W	#1,R5
  JMP w_start0

w_end0:
  MOV.W	R10,R12
  MOV.W	R9,R13
  MOV.W	R7,R14
  CALL #mont_mul
  MOV.W	R10,R12
  ADD.W	#384,R12
  MOV.W	#n,R11

w_start1:
	CMP.W	R12,R10
	JGE	w_end1
  MOV.W	@R10+,R7
  MOV.W	@R11+,R8
  SUBC.W	R8,R7
  JMP w_start1

w_end1:
  MOV.W	#0,R7
  ADDC.W	R7,R7
  ADD.W	#-384,R12
  MOV.W	#0,R8
	CMP.W	R8,R7
	JEQ	if_true2
  JMP if_end2

if_true2:
  CALL #sub_mod

if_end2:
  POPM.W	#7,R10
  RET

mont_mul:
  PUSHM.W	#4,R10
  MOV.W	R12,R8
  ADD.W	#384,R8
  MOV.W	#0,R9

w_start3:
	CMP.W	R8,R12
	JGE	w_end3
  MOV.W	R9,0(R12)
  ADD.W	#2,R12
  JMP w_start3

w_end3:
  ADD.W	#-384,R8
  MOV.W	R13,R9
  MOV.W	R14,R10
  MOV.W	R9,R7
  ADD.W	#384,R7

w_start4:
	CMP.W	R7,R9
	JGE	w_end4
  MOV.W	R8,R12
  MOV.W	@R9+,R13
  MOV.W	R10,R14
  CALL #mont_mul_add
  JMP w_start4

w_end4:
  POPM.W	#4,R10
  RET

mont_mul_add:
  PUSHM.W	#7,R10
  SUB.W	#2,SP
  MOV.W	R12,R8
  MOV.W	R13,R5
  MOV.W	R14,R6
  MOV.W	@R12,R14
  MOV.W	@R6+,R13
  MOV.W	R5,R12
  CALL #mula16
  MOV.W	R12,R10
  MOV.W	R13,R9
  MOV.W	#29151,R13
  CALL #__mspabi_mpyi
  MOV.W	R12,R4
  MOV.W	#n,R7
  MOV.W	@R7+,R13
  MOV.W	R10,R14
  CALL #mula16
  MOV.W	R13,R10
  MOV.W	R7,R15
  ADD.W	#382,R15
  MOV.W	R15,0(SP)

w_start5:
	CMP.W	R15,R7
	JGE	w_end5
  MOV.W	R5,R12
  MOV.W	@R6+,R13
  MOV.W	R8,R15
  ADD.W	#2,R15
  MOV.W	@R15+,R14
  MOV.W	R9,R15
  CALL #mulaa16
  MOV.W	R12,R14
  MOV.W	R13,R9
  MOV.W	R4,R12
  MOV.W	@R7+,R13
  MOV.W	R10,R15
  CALL #mulaa16
  MOV.W	R12,R14
  MOV.W	R13,R10
  MOV.W	R14,0(R8)
  ADD.W	#2,R8
  MOV.W	0(SP),R15
  JMP w_start5

w_end5:
  MOV.W	#0,R15
  ADD.W	R10,R9
  ADDC.W	R15,R15
  MOV.W	R9,0(R8)
  ADD.W	#2,R8
	CMP.W	R10,R9
	JLO	if_true6
  JMP if_end6

if_true6:
  ADD.W	#-384,R8
  MOV.W	R8,R12
  CALL #sub_mod

if_end6:
  ADD.W	#2,SP
  POPM.W	#7,R10
  RET

mula16:
  PUSHM.W	#1,R10
  MOV.W	R14,R10
  MOV.W	R13,R14
  MOV.W	#0,R15
  MOV.W	#0,R13
  CALL #__mspabi_mpyl
  MOV.W	#0,R11
  ADD.W	R10,R12
  ADDC.W	R11,R13
  POPM.W	#1,R10
  RET

mulaa16:
  PUSHM.W	#2,R10
  MOV.W	R14,R10
  MOV.W	R15,R9
  MOV.W	R13,R14
  MOV.W	#0,R15
  MOV.W	#0,R13
  CALL #__mspabi_mpyl
  MOV.W	R10,R14
  MOV.W	#0,R15
  ADD.W	R14,R12
  ADDC.W	R15,R13
  MOV.W	R9,R10
  MOV.W	#0,R11
  ADD.W	R10,R12
  ADDC.W	R11,R13
  POPM.W	#2,R10
  RET

sub_mod:
  PUSHM.W	#4,R10
  MOV.W	R12,R7
  ADD.W	#384,R7
  SUBC.W	R9,R9
  MOV.W	#n,R13

w_start7:
	CMP.W	R7,R12
	JGE	w_end7
  MOV.W	@R12+,R9
  MOV.W	@R13+,R10
  SUBC.W	R10,R9
  MOV.W	R9,-2(R12)
  JMP w_start7

w_end7:
  POPM.W	#4,R10
  RET

