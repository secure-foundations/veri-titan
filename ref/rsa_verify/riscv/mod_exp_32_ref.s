	.file	"mod_exp_32_ref.c"
	.option nopic
	.attribute arch, "rv32i2p0_m2p0"
	.attribute unaligned_access, 0
	.attribute stack_align, 16
	.text
	.align	2
	.globl	mul32
	.type	mul32, @function
mul32:
	mv	a5,a1
	mulhu	a1,a0,a1
	mul	a0,a0,a5
	ret
	.size	mul32, .-mul32
	.align	2
	.globl	mula32
	.type	mula32, @function
mula32:
	mul	a5,a0,a1
	mulhu	a1,a0,a1
	add	a0,a5,a2
	sltu	a5,a0,a5
	add	a1,a5,a1
	ret
	.size	mula32, .-mula32
	.align	2
	.globl	mulaa32
	.type	mulaa32, @function
mulaa32:
	mul	a4,a0,a1
	add	a3,a2,a3
	sltu	a2,a3,a2
	mulhu	a5,a0,a1
	add	a0,a4,a3
	sltu	a1,a0,a4
	add	a5,a5,a2
	add	a1,a1,a5
	ret
	.size	mulaa32, .-mulaa32
	.align	2
	.globl	sub_mod
	.type	sub_mod, @function
sub_mod:
	addi	a6,a0,384
	li	a5,0
	li	a2,0
.L6:
	lw	a4,0(a0)
	lw	a3,0(a1)
	addi	a0,a0,4
	add	a5,a4,a5
	sub	a3,a5,a3
	sltu	a4,a5,a4
	add	a4,a4,a2
	sgtu	a5,a3,a5
	sub	a5,a4,a5
	sw	a3,-4(a0)
	srai	a2,a5,31
	addi	a1,a1,4
	bne	a6,a0,.L6
	ret
	.size	sub_mod, .-sub_mod
	.align	2
	.globl	ge_mod
	.type	ge_mod, @function
ge_mod:
	addi	a5,a0,380
	addi	a1,a1,380
	j	.L10
.L14:
	bgtu	a3,a4,.L12
	beq	a0,a5,.L12
	mv	a5,a2
.L10:
	lw	a4,0(a1)
	lw	a3,0(a5)
	addi	a2,a5,-4
	addi	a1,a1,-4
	bgeu	a3,a4,.L14
	li	a0,0
	ret
.L12:
	li	a0,1
	ret
	.size	ge_mod, .-ge_mod
	.align	2
	.globl	mont_mul_add
	.type	mont_mul_add, @function
mont_mul_add:
	lw	t2,0(a3)
	lw	a5,0(a1)
	lw	a7,0(a4)
	mul	a6,a2,t2
	addi	t3,a3,4
	addi	t0,a3,384
	addi	sp,sp,-16
	sw	s0,12(sp)
	mv	t4,a1
	addi	t5,a4,4
	mv	t1,a1
	add	a5,a6,a5
	mul	t6,a0,a5
	sltu	a6,a5,a6
	mul	a3,t6,a7
	mulhu	t2,a2,t2
	add	a5,a3,a5
	sltu	a5,a5,a3
	mulhu	a7,t6,a7
	add	a6,a6,t2
	add	a5,a5,a7
.L16:
	lw	s0,0(t3)
	lw	t2,0(t5)
	lw	a3,4(t1)
	mul	a0,a2,s0
	addi	t1,t1,4
	add	a3,a6,a3
	sltu	a6,a3,a6
	addi	t3,t3,4
	addi	t5,t5,4
	mul	a7,t6,t2
	add	a0,a3,a0
	sltu	a3,a0,a3
	mulhu	s0,a2,s0
	add	a5,a7,a5
	add	a0,a5,a0
	sltu	a7,a5,a7
	sw	a0,-4(t1)
	sltu	a5,a0,a5
	mulhu	t2,t6,t2
	add	a6,a6,s0
	add	a6,a3,a6
	add	a7,a7,t2
	add	a5,a5,a7
	bne	t0,t3,.L16
	add	a5,a6,a5
	sw	a5,380(a1)
	bgeu	a5,a6,.L15
	addi	a1,a1,384
	li	a5,0
	li	a0,0
.L19:
	lw	a3,0(t4)
	lw	a2,0(a4)
	addi	t4,t4,4
	add	a5,a3,a5
	sub	a2,a5,a2
	sltu	a3,a5,a3
	add	a3,a3,a0
	sgtu	a5,a2,a5
	sub	a5,a3,a5
	sw	a2,-4(t4)
	srai	a0,a5,31
	addi	a4,a4,4
	bne	a1,t4,.L19
.L15:
	lw	s0,12(sp)
	addi	sp,sp,16
	jr	ra
	.size	mont_mul_add, .-mont_mul_add
	.align	2
	.globl	mont_mul
	.type	mont_mul, @function
mont_mul:
	addi	sp,sp,-32
	sw	s1,20(sp)
	mv	s1,a1
	sw	s0,24(sp)
	sw	s4,8(sp)
	mv	s0,a2
	mv	s4,a0
	li	a2,384
	li	a1,0
	mv	a0,s1
	sw	s2,16(sp)
	sw	s3,12(sp)
	sw	s5,4(sp)
	sw	ra,28(sp)
	mv	s3,a3
	mv	s2,a4
	addi	s5,s0,384
	call	memset
.L24:
	lw	a2,0(s0)
	mv	a4,s2
	addi	s0,s0,4
	mv	a3,s3
	mv	a1,s1
	mv	a0,s4
	call	mont_mul_add
	bne	s5,s0,.L24
	lw	ra,28(sp)
	lw	s0,24(sp)
	lw	s1,20(sp)
	lw	s2,16(sp)
	lw	s3,12(sp)
	lw	s4,8(sp)
	lw	s5,4(sp)
	addi	sp,sp,32
	jr	ra
	.size	mont_mul, .-mont_mul
	.align	2
	.globl	mod_pow
	.type	mod_pow, @function
mod_pow:
	addi	sp,sp,-48
	sw	s4,24(sp)
	mv	s4,a2
	sw	s3,28(sp)
	sw	s7,12(sp)
	sw	s8,8(sp)
	mv	s3,a0
	mv	s8,a5
	mv	s7,a1
	li	a2,384
	li	a1,0
	mv	a0,s4
	sw	s0,40(sp)
	sw	s1,36(sp)
	sw	s2,32(sp)
	sw	s5,20(sp)
	sw	s6,16(sp)
	sw	ra,44(sp)
	sw	s9,4(sp)
	mv	s5,a3
	mv	s2,a4
	addi	s1,s4,384
	call	memset
	mv	s0,s8
	addi	s6,s8,384
.L28:
	lw	a2,0(s0)
	mv	a4,s2
	addi	s0,s0,4
	mv	a3,s5
	mv	a1,s4
	mv	a0,s3
	call	mont_mul_add
	bne	s6,s0,.L28
	li	s9,8
	addi	s5,s4,768
.L29:
	li	a2,384
	li	a1,0
	mv	a0,s1
	call	memset
	mv	s6,s4
	mv	s0,s4
.L30:
	lw	a2,0(s0)
	mv	a4,s2
	addi	s0,s0,4
	mv	a3,s4
	mv	a1,s1
	mv	a0,s3
	call	mont_mul_add
	bne	s1,s0,.L30
	li	a2,384
	li	a1,0
	mv	a0,s4
	call	memset
	mv	s0,s1
.L31:
	lw	a2,0(s0)
	mv	a4,s2
	addi	s0,s0,4
	mv	a3,s1
	mv	a1,s4
	mv	a0,s3
	call	mont_mul_add
	bne	s5,s0,.L31
	addi	s9,s9,-1
	bne	s9,zero,.L29
	li	a2,384
	li	a1,0
	mv	a0,s7
	call	memset
.L33:
	lw	a2,0(s6)
	mv	a4,s2
	addi	s6,s6,4
	mv	a3,s8
	mv	a1,s7
	mv	a0,s3
	call	mont_mul_add
	bne	s6,s1,.L33
	addi	a5,s7,380
	addi	a4,s2,380
	mv	a3,s7
	j	.L36
.L46:
	bgtu	a1,a2,.L35
	beq	s7,a5,.L35
	mv	a5,a0
.L36:
	lw	a2,0(a4)
	lw	a1,0(a5)
	addi	a0,a5,-4
	addi	a4,a4,-4
	bgeu	a1,a2,.L46
.L27:
	lw	ra,44(sp)
	lw	s0,40(sp)
	lw	s1,36(sp)
	lw	s2,32(sp)
	lw	s3,28(sp)
	lw	s4,24(sp)
	lw	s5,20(sp)
	lw	s6,16(sp)
	lw	s7,12(sp)
	lw	s8,8(sp)
	lw	s9,4(sp)
	addi	sp,sp,48
	jr	ra
.L35:
	addi	s7,s7,384
	li	a5,0
	li	a1,0
.L37:
	lw	a4,0(a3)
	lw	a2,0(s2)
	addi	a3,a3,4
	add	a5,a4,a5
	sub	a2,a5,a2
	sltu	a4,a5,a4
	add	a4,a4,a1
	sgtu	a5,a2,a5
	sub	a5,a4,a5
	sw	a2,-4(a3)
	srai	a1,a5,31
	addi	s2,s2,4
	bne	a3,s7,.L37
	j	.L27
	.size	mod_pow, .-mod_pow
	.ident	"GCC: (GNU) 11.1.0"
