	.file	"hello.c"
.text
	.global	__mspabi_mpyl
	.balign 2
	.global	mul32
	.type	mul32, @function
mul32:
; start of function
; framesize_regs:     0
; framesize_locals:   0
; framesize_outgoing: 0
; framesize:          0
; elim ap -> fp       2
; elim fp -> sp       0
; saved regs:(none)
	; start of prologue
	; end of prologue
	MOV.W	R13,R14 { MOV.W	#0,R15
	MOV.W	#0,R13
	CALL	#__mspabi_mpyl
	; start of epilogue
	RET
	.size	mul32, .-mul32
	.balign 2
	.global	mula32
	.type	mula32, @function
mula32:
; start of function
; framesize_regs:     2
; framesize_locals:   0
; framesize_outgoing: 0
; framesize:          2
; elim ap -> fp       4
; elim fp -> sp       0
; saved regs: R10
	; start of prologue
	PUSHM.W	#1, R10
	; end of prologue
	MOV.W	R14, R10
	MOV.W	R13,R14 { MOV.W	#0,R15
	MOV.W	#0,R13
	CALL	#__mspabi_mpyl
	MOV.W	#0,R11
	ADD	R10, R12 ; cy
	ADDC	R11, R13
	; start of epilogue
	POPM.W	#1, r10
	RET
	.size	mula32, .-mula32
	.balign 2
	.global	mulaa32
	.type	mulaa32, @function
mulaa32:
; start of function
; framesize_regs:     4
; framesize_locals:   0
; framesize_outgoing: 0
; framesize:          4
; elim ap -> fp       6
; elim fp -> sp       0
; saved regs: R9 R10
	; start of prologue
	PUSHM.W	#2, R10
	; end of prologue
	MOV.W	R14, R10
	MOV.W	R15, R9
	MOV.W	R13,R14 { MOV.W	#0,R15
	MOV.W	#0,R13
	CALL	#__mspabi_mpyl
	MOV.W	R10,R14 { MOV.W	#0,R15
	MOV.W	R9,R10 { MOV.W	#0,R11
	ADD	R10, R14 ; cy
	ADDC	R11, R15
	ADD	R14, R12 ; cy
	ADDC	R15, R13
	; start of epilogue
	POPM.W	#2, r10
	RET
	.size	mulaa32, .-mulaa32
	.balign 2
	.global	sub_mod
	.type	sub_mod, @function
sub_mod:
; start of function
; framesize_regs:     8
; framesize_locals:   0
; framesize_outgoing: 0
; framesize:          8
; elim ap -> fp       10
; elim fp -> sp       0
; saved regs: R7 R8 R9 R10
	; start of prologue
	PUSHM.W	#4, R10
	; end of prologue
	MOV.W	R12, R7
	ADD.W	#384, R7
	MOV.B	#0, R14
	MOV.B	#0, R15
.L6:
	MOV.W	@R12+, R9
	MOV.W	R9,R10 { MOV.W	#0,R11
	MOV.W	R10, R8
	ADD	R14, R8 ; cy
	MOV.W	R11, R9
	ADDC	R15, R9
	MOV.W	@R13+, R10
	MOV.W	R10,R14 { MOV.W	#0,R15
	MOV.W	R8, R10
	MOV.W	R9, R11
	SUB	R14, R10 { SUBC	R15, R11
	MOV.W	R11, R14
	MOV.W	R10, -2(R12)
	MOV.W	R11, R15
	RPT	#15 { RRAX.W	R15
	CMP.W	R12, R7 { JNE	.L6
	; start of epilogue
	POPM.W	#4, r10
	RET
	.size	sub_mod, .-sub_mod
	.balign 2
	.global	ge_mod
	.type	ge_mod, @function
ge_mod:
; start of function
; framesize_regs:     0
; framesize_locals:   0
; framesize_outgoing: 0
; framesize:          0
; elim ap -> fp       2
; elim fp -> sp       0
; saved regs:(none)
	; start of prologue
	; end of prologue
	MOV.W	R12, R14
	ADD.W	#382, R14
	ADD.W	#382, R13
	BR	#.L10
.L14:
	CMP.W	R11, R15 { JLO	.L12
	MOV.W	R14, R15
	ADD.W	#-2, R15
	ADD.W	#-2, R13
	CMP.W	R14, R12 { JEQ	.L12
	MOV.W	R15, R14
.L10:
	MOV.W	@R14, R11
	MOV.W	@R13, R15
	CMP.W	R15, R11 { JHS	.L14
	MOV.B	#0, R12
	; start of epilogue
	RET
.L12:
	MOV.B	#1, R12
	; start of epilogue
	RET
	.size	ge_mod, .-ge_mod
	.global	__mspabi_mpyi
	.balign 2
	.global	mont_mul_add
	.type	mont_mul_add, @function
mont_mul_add:
; start of function
; framesize_regs:     14
; framesize_locals:   6
; framesize_outgoing: 0
; framesize:          20
; elim ap -> fp       16
; elim fp -> sp       6
; saved regs: R4 R5 R6 R7 R8 R9 R10
	; start of prologue
	PUSHM.W	#7, R10
	SUB.W	#6, R1
	; end of prologue
	MOV.W	R12, R8
	MOV.W	R13, 4(R1)
	MOV.W	R14, R5
	MOV.W	@R13, R14
	MOV.W	R15, R6
	MOV.W	@R6+, R13
	MOV.W	R5, R12
	MOV.W	R15, @R1
	CALL	#mula32
	MOV.W	R12, R10
	MOV.W	R13, R9
	MOV.W	R8, R13
	CALL	#__mspabi_mpyi
	MOV.W	R12, R4
	MOV.W	R10, R14
	MOV.W	22(R1), R7
	MOV.W	@R7+, R13
	CALL	#mula32
	MOV.W	R13, R10
	MOV.W	4(R1), R8
	MOV.W	@R1, R15
	ADD.W	#384, R15
	MOV.W	R15, 2(R1)
.L16:
	MOV.W	R9, R15
	MOV.W	2(R8), R14
	MOV.W	@R6+, R13
	MOV.W	R5, R12
	CALL	#mulaa32
	MOV.W	R13, R9
	MOV.W	R10, R15
	MOV.W	R12, R14
	MOV.W	@R7+, R13
	MOV.W	R4, R12
	CALL	#mulaa32
	MOV.W	R13, R10
	MOV.W	R12, @R8
	ADD.W	#2, R8
	CMP.W	R6, 2(R1) { JNE	.L16
	MOV.B	#0, R15
	MOV.B	#0, R12
	ADD	R9, R13 ; cy
	ADDC	R15, R12
	MOV.W	4(R1), R14
	MOV.W	R13, 382(R14)
	CMP.W	#0, R12 { JNE	.L23
	; start of epilogue
	ADD.W	#6, R1
	POPM.W	#7, r10
	RET
.L23:
	MOV.W	22(R1), R13
	MOV.W	R14, R12
	CALL	#sub_mod
	; start of epilogue
	ADD.W	#6, R1
	POPM.W	#7, r10
	RET
	.size	mont_mul_add, .-mont_mul_add
	.balign 2
	.global	mont_mul
	.type	mont_mul, @function
mont_mul:
; start of function
; framesize_regs:     12
; framesize_locals:   0
; framesize_outgoing: 2
; framesize:          14
; elim ap -> fp       14
; elim fp -> sp       2
; saved regs: R5 R6 R7 R8 R9 R10
	; start of prologue
	PUSHM.W	#6, R10
	SUB.W	#2, R1
	; end of prologue
	MOV.W	R12, R7
	MOV.W	R13, R9
	MOV.W	R14, R10
	MOV.W	R15, R8
	MOV.W	16(R1), R5
	MOV.W	#384, R14
	MOV.B	#0, R13
	MOV.W	R9, R12
	CALL	#memset
	MOV.W	R10, R6
	ADD.W	#384, R6
.L25:
	MOV.W	R5, @R1
	MOV.W	R8, R15
	MOV.W	@R10+, R14
	MOV.W	R9, R13
	MOV.W	R7, R12
	CALL	#mont_mul_add
	CMP.W	R10, R6 { JNE	.L25
	; start of epilogue
	ADD.W	#2, R1
	POPM.W	#6, r10
	RET
	.size	mont_mul, .-mont_mul
	.balign 2
	.global	mod_pow
	.type	mod_pow, @function
mod_pow:
; start of function
; framesize_regs:     14
; framesize_locals:   0
; framesize_outgoing: 2
; framesize:          16
; elim ap -> fp       16
; elim fp -> sp       2
; saved regs: R4 R5 R6 R7 R8 R9 R10
	; start of prologue
	PUSHM.W	#7, R10
	SUB.W	#2, R1
	; end of prologue
	MOV.W	R12, R6
	MOV.W	R13, R5
	MOV.W	R14, R10
	MOV.W	18(R1), R7
	MOV.W	20(R1), R4
	MOV.W	R14, R8
	ADD.W	#384, R8
	MOV.W	R7, @R1
	MOV.W	R4, R14
	MOV.W	R10, R13
	CALL	#mont_mul
	MOV.B	#8, R9
.L28:
	MOV.W	R7, @R1
	MOV.W	R10, R15
	MOV.W	R10, R14
	MOV.W	R8, R13
	MOV.W	R6, R12
	CALL	#mont_mul
	MOV.W	R7, @R1
	MOV.W	R8, R15
	MOV.W	R8, R14
	MOV.W	R10, R13
	MOV.W	R6, R12
	CALL	#mont_mul
	ADD.W	#-1, R9
	CMP.W	#0, R9 { JNE	.L28
	MOV.W	R7, @R1
	MOV.W	R4, R15
	MOV.W	R10, R14
	MOV.W	R5, R13
	MOV.W	R6, R12
	CALL	#mont_mul
	MOV.W	R7, R13
	MOV.W	R5, R12
	CALL	#ge_mod
	CMP.W	#0, R12 { JNE	.L34
	; start of epilogue
	ADD.W	#2, R1
	POPM.W	#7, r10
	RET
.L34:
	MOV.W	R7, R13
	MOV.W	R5, R12
	CALL	#sub_mod
	; start of epilogue
	ADD.W	#2, R1
	POPM.W	#7, r10
	RET
	.size	mod_pow, .-mod_pow
	.ident	"GCC: (Mitto Systems Limited - msp430-gcc 9.3.1.11) 9.3.1"
	.mspabi_attribute 4, 2
	.mspabi_attribute 6, 1
	.mspabi_attribute 8, 1
	.gnu_attribute 4, 1