barrett384:
  /* Compute 2^129-1 mask. Could be pre-calculated for the cost of a register.
     Currently w30 is clobbered later in this subroutine. */
  bn.subi w30, w31, 1
  bn.rshi w30, w30, w31 >> 127

  /* Compute r1 = x % 2^385
     r1 = [w22, w21] = x % 2^385 = x & (2^3851)
        = ([w9, w8] * [w13,w12]) & [w30, w31]
     => max length r1: 385 bits */
  bn.mov w21, w16
  bn.and w22, w17, w30

  /* Compute q1 = x >> 383
     q1 = [w9, w8] = [w18, w17, w16] >> 383  = [w18, w17] >> 127
     => max length q1: 385 bits */
  bn.rshi w9, w18, w31 >> 127
  bn.rshi w8, w17, w18 >> 127
