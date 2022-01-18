.section .text
.globl asm_mod_pow

asm_mod_pow:
  addi sp, sp, -32
  sw ra, 28(sp)
  sw s0, 24(sp)
  sw s11, 20(sp)
  sw s2, 16(sp)
  sw s3, 12(sp)
  sw s4, 8(sp)
  sw s5, 4(sp)
  addi s0, a2, 0
  lui a2, 17
  addi a2, a2, 1560
  addi s5, a2, 768
  addi a2, a2, 384
  addi s4, a1, 0
  addi a3, s5, 0
  addi a1, s0, 0
  addi s3, a0, 0
  addi s2, s0, 384
  addi sp, sp, -32
  sw ra, 28(sp)
  sw s0, 24(sp)
  sw s11, 20(sp)
  sw s2, 16(sp)
  sw s3, 12(sp)
  sw s4, 8(sp)
  addi s0, a0, 0
  addi s11, a1, 0
  addi s2, a2, 0
  addi s3, a3, 0
  addi s4, s11, 384

w_start0:
  bge s11, s4, w_end0
  sw x0, 0(s11)
  addi s11, s11, 4
  j w_start0

w_end0:
  addi s11, a1, 0
  addi s4, s2, 384

w_start1:
  bge s2, s4, w_end1
  addi a1, s11, 0
  addi a0, s0, 0
  addi a3, s3, 0
  lw a2, 0(s2)
  addi sp, sp, -48
  sw ra, 44(sp)
  sw s0, 40(sp)
  sw s11, 36(sp)
  sw s2, 32(sp)
  sw s3, 28(sp)
  sw s4, 24(sp)
  sw s6, 16(sp)
  sw s5, 20(sp)
  sw s7, 12(sp)
  sw s8, 8(sp)
  addi s6, a1, 0
  lw a1, 0(a3)
  addi s7, a2, 0
  lw a2, 0(s6)
  addi s5, a0, 0
  addi a0, s7, 0
  addi s4, a3, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  mul s5, a0, s5
  lui s8, 17
  addi s8, s8, 1560
  addi s0, a1, 0
  lw a1, 0(s8)
  addi a2, a0, 0
  addi s2, s8, 4
  addi s4, s4, 4
  addi s3, s6, 0
  addi s8, s8, 384
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  addi s11, a1, 0

w_start2:
  bge s2, s8, w_end2
  lw a2, 4(s3)
  lw a1, 0(s4)
  addi a3, s0, 0
  addi a0, s7, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  addi s0, a1, 0
  lw a1, 0(s2)
  addi a2, a0, 0
  addi a3, s11, 0
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  sw a0, 0(s3)
  addi s2, s2, 4
  addi s11, a1, 0
  addi s4, s4, 4
  addi s3, s3, 4
  j w_start2

w_end2:
  add s0, s0, s11
  sw s0, 0(s3)
  blt s0, s11, if_true3
  j if_end3

if_true3:
  addi a0, s6, 0
  lui a2, 17
  addi a2, a2, 1560
  addi a6, a2, 384
  li a5, 0
  li a1, 0

w_start4:
  beq a2, a6, w_end4
  lw a4, 0(a0)
  lw a3, 0(a2)
  addi a2, a2, 4
  add a5, a5, a4
  sub a3, a5, a3
  sltu a4, a5, a4
  add a4, a4, a1
  sltu a5, a5, a3
  sw a3, 0(a0)
  addi a0, a0, 4
  sub a5, a4, a5
  srai a1, a5, 31
  j w_start4

w_end4:

if_end3:
  lw ra, 44(sp)
  lw s0, 40(sp)
  lw s11, 36(sp)
  lw s2, 32(sp)
  lw s3, 28(sp)
  lw s4, 24(sp)
  lw s5, 20(sp)
  lw s6, 16(sp)
  lw s7, 12(sp)
  lw s8, 8(sp)
  addi sp, sp, 48
  addi s2, s2, 4
  j w_start1

w_end1:
  lw ra, 28(sp)
  lw s0, 24(sp)
  lw s11, 20(sp)
  lw s2, 16(sp)
  lw s3, 12(sp)
  lw s4, 8(sp)
  addi sp, sp, 32
  li s11, 8

w_start5:
  ble s11, x0, w_end5
  addi a3, s0, 0
  addi a2, s0, 0
  addi a1, s2, 0
  addi a0, s3, 0
  addi sp, sp, -32
  sw ra, 28(sp)
  sw s0, 24(sp)
  sw s11, 20(sp)
  sw s2, 16(sp)
  sw s3, 12(sp)
  sw s4, 8(sp)
  addi s0, a0, 0
  addi s11, a1, 0
  addi s2, a2, 0
  addi s3, a3, 0
  addi s4, s11, 384

w_start6:
  bge s11, s4, w_end6
  sw x0, 0(s11)
  addi s11, s11, 4
  j w_start6

w_end6:
  addi s11, a1, 0
  addi s4, s2, 384

w_start7:
  bge s2, s4, w_end7
  addi a1, s11, 0
  addi a0, s0, 0
  addi a3, s3, 0
  lw a2, 0(s2)
  addi sp, sp, -48
  sw ra, 44(sp)
  sw s0, 40(sp)
  sw s11, 36(sp)
  sw s2, 32(sp)
  sw s3, 28(sp)
  sw s4, 24(sp)
  sw s6, 16(sp)
  sw s5, 20(sp)
  sw s7, 12(sp)
  sw s8, 8(sp)
  addi s6, a1, 0
  lw a1, 0(a3)
  addi s7, a2, 0
  lw a2, 0(s6)
  addi s5, a0, 0
  addi a0, s7, 0
  addi s4, a3, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  mul s5, a0, s5
  lui s8, 17
  addi s8, s8, 1560
  addi s0, a1, 0
  lw a1, 0(s8)
  addi a2, a0, 0
  addi s2, s8, 4
  addi s4, s4, 4
  addi s3, s6, 0
  addi s8, s8, 384
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  addi s11, a1, 0

w_start8:
  bge s2, s8, w_end8
  lw a2, 4(s3)
  lw a1, 0(s4)
  addi a3, s0, 0
  addi a0, s7, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  addi s0, a1, 0
  lw a1, 0(s2)
  addi a2, a0, 0
  addi a3, s11, 0
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  sw a0, 0(s3)
  addi s2, s2, 4
  addi s11, a1, 0
  addi s4, s4, 4
  addi s3, s3, 4
  j w_start8

w_end8:
  add s0, s0, s11
  sw s0, 0(s3)
  blt s0, s11, if_true9
  j if_end9

if_true9:
  addi a0, s6, 0
  lui a2, 17
  addi a2, a2, 1560
  addi a6, a2, 384
  li a5, 0
  li a1, 0

w_start10:
  beq a2, a6, w_end10
  lw a4, 0(a0)
  lw a3, 0(a2)
  addi a2, a2, 4
  add a5, a5, a4
  sub a3, a5, a3
  sltu a4, a5, a4
  add a4, a4, a1
  sltu a5, a5, a3
  sw a3, 0(a0)
  addi a0, a0, 4
  sub a5, a4, a5
  srai a1, a5, 31
  j w_start10

w_end10:

if_end9:
  lw ra, 44(sp)
  lw s0, 40(sp)
  lw s11, 36(sp)
  lw s2, 32(sp)
  lw s3, 28(sp)
  lw s4, 24(sp)
  lw s5, 20(sp)
  lw s6, 16(sp)
  lw s7, 12(sp)
  lw s8, 8(sp)
  addi sp, sp, 48
  addi s2, s2, 4
  j w_start7

w_end7:
  lw ra, 28(sp)
  lw s0, 24(sp)
  lw s11, 20(sp)
  lw s2, 16(sp)
  lw s3, 12(sp)
  lw s4, 8(sp)
  addi sp, sp, 32
  addi a3, s2, 0
  addi a2, s2, 0
  addi a1, s0, 0
  addi a0, s3, 0
  addi sp, sp, -32
  sw ra, 28(sp)
  sw s0, 24(sp)
  sw s11, 20(sp)
  sw s2, 16(sp)
  sw s3, 12(sp)
  sw s4, 8(sp)
  addi s0, a0, 0
  addi s11, a1, 0
  addi s2, a2, 0
  addi s3, a3, 0
  addi s4, s11, 384

w_start11:
  bge s11, s4, w_end11
  sw x0, 0(s11)
  addi s11, s11, 4
  j w_start11

w_end11:
  addi s11, a1, 0
  addi s4, s2, 384

w_start12:
  bge s2, s4, w_end12
  addi a1, s11, 0
  addi a0, s0, 0
  addi a3, s3, 0
  lw a2, 0(s2)
  addi sp, sp, -48
  sw ra, 44(sp)
  sw s0, 40(sp)
  sw s11, 36(sp)
  sw s2, 32(sp)
  sw s3, 28(sp)
  sw s4, 24(sp)
  sw s6, 16(sp)
  sw s5, 20(sp)
  sw s7, 12(sp)
  sw s8, 8(sp)
  addi s6, a1, 0
  lw a1, 0(a3)
  addi s7, a2, 0
  lw a2, 0(s6)
  addi s5, a0, 0
  addi a0, s7, 0
  addi s4, a3, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  mul s5, a0, s5
  lui s8, 17
  addi s8, s8, 1560
  addi s0, a1, 0
  lw a1, 0(s8)
  addi a2, a0, 0
  addi s2, s8, 4
  addi s4, s4, 4
  addi s3, s6, 0
  addi s8, s8, 384
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  addi s11, a1, 0

w_start13:
  bge s2, s8, w_end13
  lw a2, 4(s3)
  lw a1, 0(s4)
  addi a3, s0, 0
  addi a0, s7, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  addi s0, a1, 0
  lw a1, 0(s2)
  addi a2, a0, 0
  addi a3, s11, 0
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  sw a0, 0(s3)
  addi s2, s2, 4
  addi s11, a1, 0
  addi s4, s4, 4
  addi s3, s3, 4
  j w_start13

w_end13:
  add s0, s0, s11
  sw s0, 0(s3)
  blt s0, s11, if_true14
  j if_end14

if_true14:
  addi a0, s6, 0
  lui a2, 17
  addi a2, a2, 1560
  addi a6, a2, 384
  li a5, 0
  li a1, 0

w_start15:
  beq a2, a6, w_end15
  lw a4, 0(a0)
  lw a3, 0(a2)
  addi a2, a2, 4
  add a5, a5, a4
  sub a3, a5, a3
  sltu a4, a5, a4
  add a4, a4, a1
  sltu a5, a5, a3
  sw a3, 0(a0)
  addi a0, a0, 4
  sub a5, a4, a5
  srai a1, a5, 31
  j w_start15

w_end15:

if_end14:
  lw ra, 44(sp)
  lw s0, 40(sp)
  lw s11, 36(sp)
  lw s2, 32(sp)
  lw s3, 28(sp)
  lw s4, 24(sp)
  lw s5, 20(sp)
  lw s6, 16(sp)
  lw s7, 12(sp)
  lw s8, 8(sp)
  addi sp, sp, 48
  addi s2, s2, 4
  j w_start12

w_end12:
  lw ra, 28(sp)
  lw s0, 24(sp)
  lw s11, 20(sp)
  lw s2, 16(sp)
  lw s3, 12(sp)
  lw s4, 8(sp)
  addi sp, sp, 32
  addi s11, s11, -1
  j w_start5

w_end5:
  addi a0, s3, 0
  addi a3, s5, 0
  addi a2, s0, 0
  addi a1, s4, 0
  addi sp, sp, -32
  sw ra, 28(sp)
  sw s0, 24(sp)
  sw s11, 20(sp)
  sw s2, 16(sp)
  sw s3, 12(sp)
  sw s4, 8(sp)
  addi s0, a0, 0
  addi s11, a1, 0
  addi s2, a2, 0
  addi s3, a3, 0
  addi s4, s11, 384

w_start16:
  bge s11, s4, w_end16
  sw x0, 0(s11)
  addi s11, s11, 4
  j w_start16

w_end16:
  addi s11, a1, 0
  addi s4, s2, 384

w_start17:
  bge s2, s4, w_end17
  addi a1, s11, 0
  addi a0, s0, 0
  addi a3, s3, 0
  lw a2, 0(s2)
  addi sp, sp, -48
  sw ra, 44(sp)
  sw s0, 40(sp)
  sw s11, 36(sp)
  sw s2, 32(sp)
  sw s3, 28(sp)
  sw s4, 24(sp)
  sw s6, 16(sp)
  sw s5, 20(sp)
  sw s7, 12(sp)
  sw s8, 8(sp)
  addi s6, a1, 0
  lw a1, 0(a3)
  addi s7, a2, 0
  lw a2, 0(s6)
  addi s5, a0, 0
  addi a0, s7, 0
  addi s4, a3, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  mul s5, a0, s5
  lui s8, 17
  addi s8, s8, 1560
  addi s0, a1, 0
  lw a1, 0(s8)
  addi a2, a0, 0
  addi s2, s8, 4
  addi s4, s4, 4
  addi s3, s6, 0
  addi s8, s8, 384
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  addi s11, a1, 0

w_start18:
  bge s2, s8, w_end18
  lw a2, 4(s3)
  lw a1, 0(s4)
  addi a3, s0, 0
  addi a0, s7, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  addi s0, a1, 0
  lw a1, 0(s2)
  addi a2, a0, 0
  addi a3, s11, 0
  addi a0, s5, 0
  mul a5, a0, a1
  mulhu a1, a0, a1
  add a0, a5, a2
  sltu a5, a0, a5
  add a1, a1, a5
  add a0, a0, a3
  sltu a5, a0, a3
  add a1, a1, a5
  sw a0, 0(s3)
  addi s2, s2, 4
  addi s11, a1, 0
  addi s4, s4, 4
  addi s3, s3, 4
  j w_start18

w_end18:
  add s0, s0, s11
  sw s0, 0(s3)
  blt s0, s11, if_true19
  j if_end19

if_true19:
  addi a0, s6, 0
  lui a2, 17
  addi a2, a2, 1560
  addi a6, a2, 384
  li a5, 0
  li a1, 0

w_start20:
  beq a2, a6, w_end20
  lw a4, 0(a0)
  lw a3, 0(a2)
  addi a2, a2, 4
  add a5, a5, a4
  sub a3, a5, a3
  sltu a4, a5, a4
  add a4, a4, a1
  sltu a5, a5, a3
  sw a3, 0(a0)
  addi a0, a0, 4
  sub a5, a4, a5
  srai a1, a5, 31
  j w_start20

w_end20:

if_end19:
  lw ra, 44(sp)
  lw s0, 40(sp)
  lw s11, 36(sp)
  lw s2, 32(sp)
  lw s3, 28(sp)
  lw s4, 24(sp)
  lw s5, 20(sp)
  lw s6, 16(sp)
  lw s7, 12(sp)
  lw s8, 8(sp)
  addi sp, sp, 48
  addi s2, s2, 4
  j w_start17

w_end17:
  lw ra, 28(sp)
  lw s0, 24(sp)
  lw s11, 20(sp)
  lw s2, 16(sp)
  lw s3, 12(sp)
  lw s4, 8(sp)
  addi sp, sp, 32
  addi a0, s4, 0
  lui a1, 17
  addi a5, a1, 1560
  addi a0, a0, 380
  addi a5, a5, 380
  addi a1, a1, 1560
  addi a2, x0, 1

w_start21:
  beq a2, x0, w_end21
  lw a3, 0(a0)
  lw a4, 0(a5)
  sub a2, a3, a4
  sltu a3, a3, a4
  sltu a4, x0, a2
  xor a2, a1, a5
  bne a4, x0, if_true22
  j if_end22

if_true22:
  add a2, x0, x0

if_end22:
  addi a0, a0, -4
  addi a5, a5, -4
  j w_start21

w_end21:
  addi a0, a3, 0
  beq a0, x0, if_true23
  j if_end23

if_true23:
  addi a0, s4, 0
  lui a2, 17
  addi a2, a2, 1560
  addi a6, a2, 384
  li a5, 0
  li a1, 0

w_start24:
  beq a2, a6, w_end24
  lw a4, 0(a0)
  lw a3, 0(a2)
  addi a2, a2, 4
  add a5, a5, a4
  sub a3, a5, a3
  sltu a4, a5, a4
  add a4, a4, a1
  sltu a5, a5, a3
  sw a3, 0(a0)
  addi a0, a0, 4
  sub a5, a4, a5
  srai a1, a5, 31
  j w_start24

w_end24:

if_end23:
  lw ra, 28(sp)
  lw s0, 24(sp)
  lw s11, 20(sp)
  lw s2, 16(sp)
  lw s3, 12(sp)
  lw s4, 8(sp)
  lw s5, 4(sp)
  addi sp, sp, 32
