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
; framesize_locals:   16
; framesize_outgoing: 0
; framesize:          30
; elim ap -> fp       16
; elim fp -> sp       16
; saved regs: R4 R5 R6 R7 R8 R9 R10
	; start of prologue
	PUSHM.W	#7, R10
	SUB.W	#16, R1
	; end of prologue
	MOV.W	R12, R9
	MOV.W	R13, 8(R1)
	MOV.W	R15, R10
	MOV.W	R14,R11 { MOV.W	#0,R12
	MOV.W	R11, 4(R1)
	MOV.W	R12, 6(R1)
	MOV.W	R15, R4
	MOV.W	R11, R14
	MOV.W	R12, R15
	MOV.W	@R4+, R8
	MOV.W	R8,R12 { MOV.W	#0,R13
	CALL	#__mspabi_mpyl
	MOV.W	8(R1), R11
	MOV.W	@R11, R11
	MOV.W	R11,R14 { MOV.W	#0,R15
	MOV.W	R12, R8
	ADD	R14, R8 ; cy
	MOV.W	R13, R7
	ADDC	R15, R7
	MOV.W	R8, R13
	MOV.W	R9, R12
	CALL	#__mspabi_mpyi
	MOV.W	R12,R13 { MOV.W	#0,R14
	MOV.W	R13, @R1
	MOV.W	R14, 2(R1)
	MOV.W	32(R1), R6
	MOV.W	R14, R15
	MOV.W	R13, R14
	MOV.W	@R6+, R9
	MOV.W	R9,R12 { MOV.W	#0,R13
	CALL	#__mspabi_mpyl
	MOV.B	#0, R14
	ADD	R8, R12 ; cy
	MOV.W	R13, R9
	ADDC	R14, R9
	MOV.W	8(R1), R5
	ADD.W	#384, R10
	MOV.W	R5, R8
	MOV.W	R5, 10(R1)
	MOV.W	R10, R5
.L16:
	MOV.W	2(R8), R11
	MOV.W	R11,R14 { MOV.W	#0,R15
	MOV.W	R7, R10
	ADD	R14, R10 ; cy
	MOV.B	#0, R7
	ADDC	R15, R7
	MOV.W	4(R1), R14
	MOV.W	6(R1), R15
	MOV.W	@R4+, R11
	MOV.W	R11,R12 { MOV.W	#0,R13
	CALL	#__mspabi_mpyl
	ADD	R12, R10 ; cy
	ADDC	R13, R7
	MOV.W	@R1, R14
	MOV.W	2(R1), R15
	MOV.W	@R6+, R11
	MOV.W	R11,R12 { MOV.W	#0,R13
	CALL	#__mspabi_mpyl
	ADD	R9, R12 ; cy
	MOV.B	#0, R9
	ADDC	R9, R13
	ADD	R12, R10 ; cy
	ADDC	R13, R9
	MOV.W	R10, @R8
	ADD.W	#2, R8
	CMP.W	R4, R5 { JNE	.L16
	MOV.W	10(R1), R5
	ADD	R9, R7 ; cy
	MOV.B	#0, R12
	MOV.B	#0, R13
	ADDC	R13, R12
	MOV.W	8(R1), R8
	MOV.W	R7, 382(R8)
	CMP.W	#0, R12 { JEQ	.L15
	MOV.W	32(R1), R13
	MOV.W	R8, R9
	ADD.W	#384, R9
	MOV.B	#0, R12
	MOV.B	#0, R10
	MOV.W	R9, R7
.L19:
	MOV.W	@R5+, R9
	MOV.W	R9,R14 { MOV.W	#0,R15
	MOV.W	R14, R8
	ADD	R12, R8 ; cy
	MOV.W	R15, R9
	ADDC	R10, R9
	MOV.W	@R13+, R12
	MOV.W	R12,R10 { MOV.W	#0,R11
	MOV.W	R8, R14
	MOV.W	R9, R15
	SUB	R10, R14 { SUBC	R11, R15
	MOV.W	R15, R12
	MOV.W	R14, -2(R5)
	MOV.W	R15, R10
	RPT	#15 { RRAX.W	R10
	CMP.W	R5, R7 { JNE	.L19
.L15:
	; start of epilogue
	ADD.W	#16, R1
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
.L26:
	MOV.W	R5, @R1
	MOV.W	R8, R15
	MOV.W	@R10+, R14
	MOV.W	R9, R13
	MOV.W	R7, R12
	CALL	#mont_mul_add
	CMP.W	R10, R6 { JNE	.L26
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
; framesize_locals:   8
; framesize_outgoing: 2
; framesize:          24
; elim ap -> fp       16
; elim fp -> sp       10
; saved regs: R4 R5 R6 R7 R8 R9 R10
	; start of prologue
	PUSHM.W	#7, R10
	SUB.W	#10, R1
	; end of prologue
	MOV.W	R12, R8
	MOV.W	R13, 4(R1)
	MOV.W	R14, R7
	MOV.W	R15, R6
	MOV.W	26(R1), R9
	MOV.W	R14, R10
	ADD.W	#384, R10
	MOV.W	#384, R14
	MOV.B	#0, R13
	MOV.W	R7, R12
	CALL	#memset
	MOV.W	28(R1), R5
	MOV.W	R5, R4
	ADD.W	#384, R4
.L29:
	MOV.W	R9, @R1
	MOV.W	R6, R15
	MOV.W	@R5+, R14
	MOV.W	R7, R13
	MOV.W	R8, R12
	CALL	#mont_mul_add
	CMP.W	R5, R4 { JNE	.L29
	MOV.B	#8, R15
	MOV.W	R7, R6
	ADD.W	#768, R6
	MOV.W	R15, R4
.L30:
	MOV.W	#384, R14
	MOV.B	#0, R13
	MOV.W	R10, R12
	CALL	#memset
	MOV.W	R7, 2(R1)
	MOV.W	R7, R5
.L31:
	MOV.W	R9, @R1
	MOV.W	R7, R15
	MOV.W	@R5+, R14
	MOV.W	R10, R13
	MOV.W	R8, R12
	CALL	#mont_mul_add
	CMP.W	R5, R10 { JNE	.L31
	MOV.W	#384, R14
	MOV.B	#0, R13
	MOV.W	R7, R12
	CALL	#memset
	MOV.W	R10, R5
.L32:
	MOV.W	R9, @R1
	MOV.W	R10, R15
	MOV.W	@R5+, R14
	MOV.W	R7, R13
	MOV.W	R8, R12
	CALL	#mont_mul_add
	CMP.W	R5, R6 { JNE	.L32
	ADD.W	#-1, R4
	CMP.W	#0, R4 { JNE	.L30
	MOV.W	2(R1), R5
	MOV.W	#384, R14
	MOV.B	#0, R13
	MOV.W	4(R1), R12
	CALL	#memset
	MOV.W	4(R1), R7
	MOV.W	28(R1), R6
.L34:
	MOV.W	R9, @R1
	MOV.W	R6, R15
	MOV.W	@R5+, R14
	MOV.W	R7, R13
	MOV.W	R8, R12
	CALL	#mont_mul_add
	CMP.W	R10, R5 { JNE	.L34
	MOV.W	4(R1), R12
	ADD.W	#382, R12
	MOV.W	R9, R14
	ADD.W	#382, R14
	MOV.W	4(R1), R13
	MOV.W	R13, R8
	BR	#.L37
.L46:
	CMP.W	R10, R15 { JLO	.L36
	MOV.W	R12, R15
	ADD.W	#-2, R15
	ADD.W	#-2, R14
	CMP.W	R12, R8 { JEQ	.L36
	MOV.W	R15, R12
.L37:
	MOV.W	@R12, R10
	MOV.W	@R14, R15
	CMP.W	R15, R10 { JHS	.L46
	; start of epilogue
	ADD.W	#10, R1
	POPM.W	#7, r10
	RET
.L36:
	MOV.W	4(R1), R4
	ADD.W	#384, R4
	MOV.B	#0, R12
	MOV.B	#0, R10
	MOV.W	R9, R7
.L38:
	MOV.W	@R13+, R9
	MOV.W	R9,R14 { MOV.W	#0,R15
	MOV.W	R14, R8
	ADD	R12, R8 ; cy
	MOV.W	R15, R9
	ADDC	R10, R9
	MOV.W	@R7+, R12
	MOV.W	R12,R10 { MOV.W	#0,R11
	MOV.W	R8, R14
	MOV.W	R9, R15
	SUB	R10, R14 { SUBC	R11, R15
	MOV.W	R15, R12
	MOV.W	R14, -2(R13)
	MOV.W	R15, R10
	RPT	#15 { RRAX.W	R10
	CMP.W	R4, R13 { JNE	.L38
	; start of epilogue
	ADD.W	#10, R1
	POPM.W	#7, r10
	RET
	.size	mod_pow, .-mod_pow
	.ident	"GCC: (Mitto Systems Limited - msp430-gcc 9.3.1.11) 9.3.1"
	.mspabi_attribute 4, 2
	.mspabi_attribute 6, 1
	.mspabi_attribute 8, 1
	.gnu_attribute 4, 1
