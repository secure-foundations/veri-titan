	.file	"mod_pow.c"
	.option nopic
	.attribute arch, "rv32i2p0_m2p0_a2p0_f2p0_d2p0_c2p0"
	.attribute unaligned_access, 0
	.attribute stack_align, 16
	.text
	.align	1
	.type	sub_mod, @function
sub_mod:
	addi	a6,a0,384
	li	a5,0
	li	a2,0
.L2:
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
	bne	a6,a0,.L2
	ret
	.size	sub_mod, .-sub_mod
	.align	1
	.type	ge_mod, @function
ge_mod:
	addi	a5,a0,380
	addi	a1,a1,380
	j	.L7
.L11:
	bgtu	a3,a4,.L9
	beq	a0,a5,.L9
	mv	a5,a2
.L7:
	lw	a4,0(a1)
	lw	a3,0(a5)
	addi	a2,a5,-4
	addi	a1,a1,-4
	bgeu	a3,a4,.L11
	li	a0,0
	ret
.L9:
	li	a0,1
	ret
	.size	ge_mod, .-ge_mod
	.align	1
	.globl	mul32
	.type	mul32, @function
mul32:
	mv	a5,a1
	mulhu	a1,a0,a1
	mul	a0,a0,a5
	ret
	.size	mul32, .-mul32
	.align	1
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
	.align	1
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
	.align	1
	.type	mont_mul_add, @function
mont_mul_add:
	addi	sp,sp,-48
	sw	s5,20(sp)
	sw	s6,16(sp)
	mv	s5,a2
	mv	s6,a1
	lw	a2,0(a2)
	lw	a1,0(a4)
	sw	s4,24(sp)
	mv	s4,a0
	mv	a0,a3
	sw	ra,44(sp)
	sw	s0,40(sp)
	sw	s1,36(sp)
	sw	s2,32(sp)
	sw	s3,28(sp)
	sw	s7,12(sp)
	sw	s8,8(sp)
	sw	s9,4(sp)
	mv	s8,a4
	mv	s7,a3
	call	mula32
	mul	s4,a0,s4
	mv	s0,a1
	lw	a1,0(s6)
	mv	a2,a0
	addi	s9,s8,4
	mv	s2,s5
	addi	s3,s6,4
	addi	s8,s8,384
	mv	a0,s4
	call	mula32
	mv	s1,a1
.L16:
	lw	a2,4(s2)
	lw	a1,0(s9)
	mv	a3,s0
	mv	a0,s7
	call	mulaa32
	mv	s0,a1
	lw	a1,0(s3)
	mv	a2,a0
	mv	a3,s1
	mv	a0,s4
	call	mulaa32
	sw	a0,0(s2)
	addi	s9,s9,4
	mv	s1,a1
	addi	s2,s2,4
	addi	s3,s3,4
	bne	s8,s9,.L16
	add	s0,a1,s0
	sw	s0,380(s5)
	bltu	s0,a1,.L21
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
.L21:
	lw	s0,40(sp)
	lw	ra,44(sp)
	lw	s1,36(sp)
	lw	s2,32(sp)
	lw	s3,28(sp)
	lw	s4,24(sp)
	lw	s7,12(sp)
	lw	s8,8(sp)
	lw	s9,4(sp)
	mv	a1,s6
	mv	a0,s5
	lw	s6,16(sp)
	lw	s5,20(sp)
	addi	sp,sp,48
	tail	sub_mod
	.size	mont_mul_add, .-mont_mul_add
	.align	1
	.globl	mont_mul
	.type	mont_mul, @function
mont_mul:
	addi	sp,sp,-32
	sw	s1,20(sp)
	mv	s1,a2
	sw	s3,12(sp)
	sw	s4,8(sp)
	mv	s3,a1
	mv	s4,a0
	li	a2,384
	li	a1,0
	mv	a0,s1
	sw	s0,24(sp)
	sw	s2,16(sp)
	sw	s5,4(sp)
	sw	ra,28(sp)
	mv	s0,a3
	mv	s2,a4
	addi	s5,a3,384
	call	memset
.L23:
	lw	a3,0(s0)
	mv	a4,s2
	addi	s0,s0,4
	mv	a2,s1
	mv	a1,s3
	mv	a0,s4
	call	mont_mul_add
	bne	s5,s0,.L23
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
	.align	1
	.globl	mod_pow
	.type	mod_pow, @function
mod_pow:
	addi	sp,sp,-32
	sw	s3,12(sp)
	mv	s3,a4
	sw	s5,4(sp)
	mv	a4,a3
	mv	s5,a1
	mv	a3,a5
	mv	a1,s3
	sw	s0,24(sp)
	sw	s1,20(sp)
	sw	s2,16(sp)
	sw	s4,8(sp)
	sw	s6,0(sp)
	sw	ra,28(sp)
	mv	s6,a5
	mv	s0,a2
	mv	s4,a0
	addi	s2,a2,384
	li	s1,8
	call	mont_mul
.L27:
	mv	a4,s0
	mv	a3,s0
	mv	a2,s2
	mv	a1,s3
	mv	a0,s4
	call	mont_mul
	addi	s1,s1,-1
	mv	a4,s2
	mv	a3,s2
	mv	a2,s0
	mv	a1,s3
	mv	a0,s4
	call	mont_mul
	bne	s1,zero,.L27
	mv	a1,s3
	mv	a0,s4
	mv	a4,s6
	mv	a3,s0
	mv	a2,s5
	call	mont_mul
	mv	a1,s3
	mv	a0,s5
	call	ge_mod
	bne	a0,zero,.L31
	lw	ra,28(sp)
	lw	s0,24(sp)
	lw	s1,20(sp)
	lw	s2,16(sp)
	lw	s3,12(sp)
	lw	s4,8(sp)
	lw	s5,4(sp)
	lw	s6,0(sp)
	addi	sp,sp,32
	jr	ra
.L31:
	lw	s0,24(sp)
	lw	ra,28(sp)
	lw	s1,20(sp)
	lw	s2,16(sp)
	lw	s4,8(sp)
	lw	s6,0(sp)
	mv	a1,s3
	mv	a0,s5
	lw	s3,12(sp)
	lw	s5,4(sp)
	addi	sp,sp,32
	tail	sub_mod
	.size	mod_pow, .-mod_pow
	.ident	"GCC: (GNU) 10.2.0"
