	.file	"mod_exp.c"
.text
	.global	__mspabi_mpyl
	.balign 2
	.global	mul16
	.type	mul16, @function
mul16:
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
	mov.w	r13,r14 { mov.w	#0,r15
	mov.w	#0,r13
	call	#__mspabi_mpyl
	; start of epilogue
	ret
	.size	mul16, .-mul16
	.balign 2
	.global	mula16
	.type	mula16, @function
mula16:
; start of function
; framesize_regs:     2
; framesize_locals:   0
; framesize_outgoing: 0
; framesize:          2
; elim ap -> fp       4
; elim fp -> sp       0
; saved regs: r10
	; start of prologue
	pushm.w	#1, r10
	; end of prologue
	mov.w	r14, r10
	mov.w	r13,r14 { mov.w	#0,r15
	mov.w	#0,r13
	call	#__mspabi_mpyl
	mov.w	#0,r11
	add	r10, r12 ; cy
	addc	r11, r13
	; start of epilogue
	popm.w	#1, r10
	ret
	.size	mula16, .-mula16
	.balign 2
	.global	mulaa16
	.type	mulaa16, @function
mulaa16:
; start of function
; framesize_regs:     4
; framesize_locals:   0
; framesize_outgoing: 0
; framesize:          4
; elim ap -> fp       6
; elim fp -> sp       0
; saved regs: r9 r10
	; start of prologue
	pushm.w	#2, r10
	; end of prologue
	mov.w	r14, r10
	mov.w	r15, r9
	mov.w	r13,r14 { mov.w	#0,r15
	mov.w	#0,r13
	call	#__mspabi_mpyl
	mov.w	r10,r14 { mov.w	#0,r15
	mov.w	r9,r10 { mov.w	#0,r11
	add	r10, r14 ; cy
	addc	r11, r15
	add	r14, r12 ; cy
	addc	r15, r13
	; start of epilogue
	popm.w	#2, r10
	ret
	.size	mulaa16, .-mulaa16
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
; saved regs: r7 r8 r9 r10
	; start of prologue
	pushm.w	#4, r10
	; end of prologue
	mov.w	r12, r7
	add.w	#384, r7
	mov.b	#0, r14
	mov.b	#0, r15
.l6:
	mov.w	@r12+, r9
	mov.w	r9,r10 { mov.w	#0,r11
	mov.w	r10, r8
	add	r14, r8 ; cy
	mov.w	r11, r9
	addc	r15, r9
	mov.w	@r13+, r10
	mov.w	r10,r14 { mov.w	#0,r15
	mov.w	r8, r10
	mov.w	r9, r11
	sub	r14, r10 { subc	r15, r11
	mov.w	r11, r14
	mov.w	r10, -2(r12)
	mov.w	r11, r15
	rpt	#15 { rrax.w	r15
	cmp.w	r12, r7 { jne	.l6
	; start of epilogue
	popm.w	#4, r10
	ret
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
	mov.w	r12, r14
	add.w	#382, r14
	add.w	#382, r13
	br	#.l10
.l14:
	cmp.w	r11, r15 { jlo	.l12
	mov.w	r14, r15
	add.w	#-2, r15
	add.w	#-2, r13
	cmp.w	r14, r12 { jeq	.l12
	mov.w	r15, r14
.l10:
	mov.w	@r14, r11
	mov.w	@r13, r15
	cmp.w	r15, r11 { jhs	.l14
	mov.b	#0, r12
	; start of epilogue
	ret
.l12:
	mov.b	#1, r12
	; start of epilogue
	ret
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
; saved regs: r4 r5 r6 r7 r8 r9 r10
	; start of prologue
	pushm.w	#7, r10
	sub.w	#6, r1
	; end of prologue
	mov.w	r12, r8
	mov.w	r13, 4(r1)
	mov.w	r14, r5
	mov.w	@r13, r14
	mov.w	r15, r6
	mov.w	@r6+, r13
	mov.w	r5, r12
	mov.w	r15, @r1
	call	#mula16
	mov.w	r12, r10
	mov.w	r13, r9
	mov.w	r8, r13
	call	#__mspabi_mpyi
	mov.w	r12, r4
	mov.w	r10, r14
	mov.w	22(r1), r7
	mov.w	@r7+, r13
	call	#mula16
	mov.w	r13, r10
	mov.w	4(r1), r8
	mov.w	@r1, r15
	add.w	#384, r15
	mov.w	r15, 2(r1)
.l16:
	mov.w	r9, r15
	mov.w	2(r8), r14
	mov.w	@r6+, r13
	mov.w	r5, r12
	call	#mulaa16
	mov.w	r13, r9
	mov.w	r10, r15
	mov.w	r12, r14
	mov.w	@r7+, r13
	mov.w	r4, r12
	call	#mulaa16
	mov.w	r13, r10
	mov.w	r12, @r8
	add.w	#2, r8
	cmp.w	r6, 2(r1) { jne	.l16
	mov.b	#0, r15
	mov.b	#0, r12
	add	r9, r13 ; cy
	addc	r15, r12
	mov.w	4(r1), r14
	mov.w	r13, 382(r14)
	cmp.w	#0, r12 { jne	.l23
	; start of epilogue
	add.w	#6, r1
	popm.w	#7, r10
	ret
.l23:
	mov.w	22(r1), r13
	mov.w	r14, r12
	call	#sub_mod
	; start of epilogue
	add.w	#6, r1
	popm.w	#7, r10
	ret
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
; saved regs: r5 r6 r7 r8 r9 r10
	; start of prologue
	pushm.w	#6, r10
	sub.w	#2, r1
	; end of prologue
	mov.w	r12, r7
	mov.w	r13, r9
	mov.w	r14, r10
	mov.w	r15, r8
	mov.w	16(r1), r5
	mov.w	#384, r14
	mov.b	#0, r13
	mov.w	r9, r12
	call	#memset
	mov.w	r10, r6
	add.w	#384, r6
.l25:
	mov.w	r5, @r1
	mov.w	r8, r15
	mov.w	@r10+, r14
	mov.w	r9, r13
	mov.w	r7, r12
	call	#mont_mul_add
	cmp.w	r10, r6 { jne	.l25
	; start of epilogue
	add.w	#2, r1
	popm.w	#6, r10
	ret
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
; saved regs: r4 r5 r6 r7 r8 r9 r10
	; start of prologue
	pushm.w	#7, r10
	sub.w	#2, r1
	; end of prologue
	mov.w	r12, r6
	mov.w	r13, r5
	mov.w	r14, r10
	mov.w	18(r1), r7
	mov.w	20(r1), r4
	mov.w	r14, r8
	add.w	#384, r8
	mov.w	r7, @r1
	mov.w	r4, r14
	mov.w	r10, r13
	call	#mont_mul
	mov.b	#8, r9
.l28:
	mov.w	r7, @r1
	mov.w	r10, r15
	mov.w	r10, r14
	mov.w	r8, r13
	mov.w	r6, r12
	call	#mont_mul
	mov.w	r7, @r1
	mov.w	r8, r15
	mov.w	r8, r14
	mov.w	r10, r13
	mov.w	r6, r12
	call	#mont_mul
	add.w	#-1, r9
	cmp.w	#0, r9 { jne	.l28
	mov.w	r7, @r1
	mov.w	r4, r15
	mov.w	r10, r14
	mov.w	r5, r13
	mov.w	r6, r12
	call	#mont_mul
	mov.w	r7, r13
	mov.w	r5, r12
	call	#ge_mod
	cmp.w	#0, r12 { jne	.l34
	; start of epilogue
	add.w	#2, r1
	popm.w	#7, r10
	ret
.l34:
	mov.w	r7, r13
	mov.w	r5, r12
	call	#sub_mod
	; start of epilogue
	add.w	#2, r1
	popm.w	#7, r10
	ret
	.size	mod_pow, .-mod_pow
	.ident	"gcc: (mitto systems limited - msp430-gcc 9.3.1.11) 9.3.1"
	.mspabi_attribute 4, 2
	.mspabi_attribute 6, 1
	.mspabi_attribute 8, 1
	.gnu_attribute 4, 1
