.globl rv_falcon
rv_falcon:
  addi sp, sp, -28
  sw ra, 24(sp)
  sw s0, 20(sp)
  sw s1, 16(sp)
  sw s2, 12(sp)
  sw s3, 8(sp)
  sw s4, 4(sp)
  sw s5, 0(sp)
  li s1, 12289
  addi s2, a0, 0
  addi s3, a3, 0
  addi s4, a1, 0
  addi t1, a1, 1024

w_start0:
  bgeu a1, t1, w_end0
  lh t2, 0(a1)
  srai t3, t2, 31
  and t3, t3, s1
  add t2, t2, t3
  sh t2, 0(a3)
  addi a3, a3, 2
  addi a1, a1, 2
  j w_start0

w_end0:
  addi a3, a3, -1024
  addi a0, a3, 0
  addi a1, a2, 0
  addi s0, a0, 0
  addi s1, a1, 0
  call forward_ntt_std2rev
  addi a0, s1, 0
  call forward_ntt_std2rev
  addi a0, s0, 0
  addi a1, s1, 0
  addi a3, a0, 1024
  li t3, 10952

w_start1:
  bgeu a0, a3, w_end1
  lhu t0, 0(a0)
  lhu t1, 0(a1)
  mul t0, t0, t1
  slli a4, t0, 1
  add a4, a4, t0
  slli a4, a4, 12
  sub a4, a4, t0
  slli a4, a4, 16
  srli a4, a4, 16
  slli a5, a4, 1
  add a5, a5, a4
  slli a5, a5, 12
  add a5, a5, a4
  add a5, a5, t0
  srli a5, a5, 16
  li a4, 12289
  sub a5, a5, a4
  srai t0, a5, 31
  and t0, t0, a4
  add t0, t0, a5
  addi t1, t3, 0
  mul t0, t0, t1
  slli a4, t0, 1
  add a4, a4, t0
  slli a4, a4, 12
  sub a4, a4, t0
  slli a4, a4, 16
  srli a4, a4, 16
  slli a5, a4, 1
  add a5, a5, a4
  slli a5, a5, 12
  add a5, a5, a4
  add a5, a5, t0
  srli a5, a5, 16
  li a4, 12289
  sub a5, a5, a4
  srai t0, a5, 31
  and t0, t0, a4
  add t0, t0, a5
  sh t0, 0(a0)
  addi a0, a0, 2
  addi a1, a1, 2
  j w_start1

w_end1:
  addi a0, a3, -1024
  la a1, bit_rev_table_512
  addi a2, a1, 960

w_start2:
  bgeu a1, a2, w_end2
  lhu t0, 0(a1)
  lhu t1, 2(a1)
  add t0, t0, t0
  add t0, a0, t0
  add t1, t1, t1
  add t1, a0, t1
  lhu a3, 0(t0)
  lhu a4, 0(t1)
  sh a4, 0(t0)
  sh a3, 0(t1)
  addi a1, a1, 4
  j w_start2

w_end2:
  addi s0, a0, 0
  call inverse_ntt_std2rev
  addi a0, s0, 0
  la a1, bit_rev_table_512
  addi a2, a1, 960

w_start3:
  bgeu a1, a2, w_end3
  lhu t0, 0(a1)
  lhu t1, 2(a1)
  add t0, t0, t0
  add t0, a0, t0
  add t1, t1, t1
  add t1, a0, t1
  lhu a3, 0(t0)
  lhu a4, 0(t1)
  sh a4, 0(t0)
  sh a3, 0(t1)
  addi a1, a1, 4
  j w_start3

w_end3:
  addi a3, a0, 1024
  la a1, scaling_factors

w_start4:
  bgeu a0, a3, w_end4
  lhu t0, 0(a0)
  lhu t1, 0(a1)
  mul t0, t0, t1
  slli a4, t0, 1
  add a4, a4, t0
  slli a4, a4, 12
  sub a4, a4, t0
  slli a4, a4, 16
  srli a4, a4, 16
  slli a5, a4, 1
  add a5, a5, a4
  slli a5, a5, 12
  add a5, a5, a4
  add a5, a5, t0
  srli a5, a5, 16
  li a4, 12289
  sub a5, a5, a4
  srai t0, a5, 31
  and t0, t0, a4
  add t0, t0, a5
  sh t0, 0(a0)
  addi a0, a0, 2
  addi a1, a1, 2
  j w_start4

w_end4:
  addi a0, a3, -1024
  li a0, 12289
  addi s1, s3, 0
  addi s0, s2, 0
  addi sp, sp, -16
  sw ra, 12(sp)
  sw s0, 8(sp)
  sw s1, 4(sp)
  sw s2, 0(sp)
  addi s2, s1, 1024

w_start5:
  bgeu s1, s2, w_end5
  lhu a2, 0(s1)
  lhu a1, 0(s0)
  sub a3, a2, a1
  srai a4, a3, 31
  and a4, a4, a0
  add a3, a4, a3
  sh a3, 0(s1)
  addi s0, s0, 2
  addi s1, s1, 2
  j w_start5

w_end5:
  lw ra, 12(sp)
  lw s0, 8(sp)
  lw s1, 4(sp)
  lw s2, 0(sp)
  addi sp, sp, 16
  li t2, 6144
  addi a1, s3, 1024

w_start6:
  bgeu s3, a1, w_end6
  lh t1, 0(s3)
  sub t3, t2, t1
  srai t3, t3, 31
  and t3, t3, a0
  sub t1, t1, t3
  sh t1, 0(s3)
  addi s3, s3, 2
  j w_start6

w_end6:
  addi s3, s3, -1024
  li a0, 0
  li a2, 0
  addi a1, s3, 1024

w_start7:
  bgeu s3, a1, w_end7
  lh s1, 0(s3)
  mul s1, s1, s1
  add a0, a0, s1
  or a2, a2, a0
  lh s1, 0(s4)
  mul s1, s1, s1
  add a0, a0, s1
  or a2, a2, a0
  addi s3, s3, 2
  addi s4, s4, 2
  j w_start7

w_end7:
  srai a2, a2, 31
  or a0, a2, a0
  li a1, 43533782
  sltu a0, a0, a1
  lw ra, 24(sp)
  lw s0, 20(sp)
  lw s1, 16(sp)
  lw s2, 12(sp)
  lw s3, 8(sp)
  lw s4, 4(sp)
  lw s5, 0(sp)
  addi sp, sp, 28
  ret

forward_ntt_std2rev:
  addi sp, sp, -28
  sw ra, 24(sp)
  sw s0, 20(sp)
  sw s1, 16(sp)
  sw s2, 12(sp)
  sw s3, 8(sp)
  sw s4, 4(sp)
  sw s5, 0(sp)
  la s3, rev_mixed_powers_mont_table
  addi s4, a0, 0
  li t1, 4294955007
  li a0, 12289
  li s1, 9
  li t6, 1024
  li a5, 1

w_start8:
  bleu s1, x0, w_end8
  srli t6, t6, 1
  li t2, 0
  li t3, 0

w_start9:
  bgeu t2, a5, w_end9
  add s5, a5, t2
  add s5, s5, s5
  addi s2, t3, 0
  add t3, t3, t6
  add s5, s5, s3
  lhu s5, 0(s5)

w_start10:
  bgeu s2, t3, w_end10
  add t4, s4, s2
  add t5, t4, t6
  lhu a1, 0(t5)
  mul a1, a1, s5
  slli a4, a1, 1
  add a4, a4, a1
  slli a4, a4, 12
  sub a4, a4, a1
  slli a4, a4, 16
  srli a4, a4, 16
  slli a3, a4, 1
  add a3, a3, a4
  slli a3, a3, 12
  add a3, a3, a4
  add a3, a3, a1
  srli a3, a3, 16
  li a4, 12289
  sub a3, a3, a4
  srai a1, a3, 31
  and a1, a1, a4
  add a1, a1, a3
  lhu a2, 0(t4)
  sub a3, a2, a1
  srai a4, a3, 31
  and a4, a4, a0
  add a3, a4, a3
  sh a3, 0(t5)
  add a4, a2, t1
  add a4, a1, a4
  srai a3, a4, 31
  and a3, a3, a0
  add a3, a3, a4
  sh a3, 0(t4)
  addi s2, s2, 2
  j w_start10

w_end10:
  add t3, t3, t6
  addi t2, t2, 1
  j w_start9

w_end9:
  slli a5, a5, 1
  addi s1, s1, -1
  j w_start8

w_end8:
  lw ra, 24(sp)
  lw s0, 20(sp)
  lw s1, 16(sp)
  lw s2, 12(sp)
  lw s3, 8(sp)
  lw s4, 4(sp)
  lw s5, 0(sp)
  addi sp, sp, 28
  ret

inverse_ntt_std2rev:
  addi sp, sp, -28
  sw ra, 24(sp)
  sw s0, 20(sp)
  sw s1, 16(sp)
  sw s2, 12(sp)
  sw s3, 8(sp)
  sw s4, 4(sp)
  sw s5, 0(sp)
  la s3, rev_omega_inv_powers_mont_table
  addi s4, a0, 0
  li t1, 4294955007
  li a0, 12289
  li s1, 9
  li t6, 1024
  li a5, 1

w_start11:
  bleu s1, x0, w_end11
  srli t6, t6, 1
  li t2, 0
  li t3, 0

w_start12:
  bgeu t2, a5, w_end12
  add s5, a5, t2
  add s5, s5, s5
  addi s2, t3, 0
  add t3, t3, t6
  add s5, s5, s3
  lhu s5, 0(s5)

w_start13:
  bgeu s2, t3, w_end13
  add t4, s4, s2
  add t5, t4, t6
  lhu a1, 0(t5)
  mul a1, a1, s5
  slli a4, a1, 1
  add a4, a4, a1
  slli a4, a4, 12
  sub a4, a4, a1
  slli a4, a4, 16
  srli a4, a4, 16
  slli a3, a4, 1
  add a3, a3, a4
  slli a3, a3, 12
  add a3, a3, a4
  add a3, a3, a1
  srli a3, a3, 16
  li a4, 12289
  sub a3, a3, a4
  srai a1, a3, 31
  and a1, a1, a4
  add a1, a1, a3
  lhu a2, 0(t4)
  sub a3, a2, a1
  srai a4, a3, 31
  and a4, a4, a0
  add a3, a4, a3
  sh a3, 0(t5)
  add a4, a2, t1
  add a4, a1, a4
  srai a3, a4, 31
  and a3, a3, a0
  add a3, a3, a4
  sh a3, 0(t4)
  addi s2, s2, 2
  j w_start13

w_end13:
  add t3, t3, t6
  addi t2, t2, 1
  j w_start12

w_end12:
  slli a5, a5, 1
  addi s1, s1, -1
  j w_start11

w_end11:
  lw ra, 24(sp)
  lw s0, 20(sp)
  lw s1, 16(sp)
  lw s2, 12(sp)
  lw s3, 8(sp)
  lw s4, 4(sp)
  lw s5, 0(sp)
  addi sp, sp, 28
  ret
