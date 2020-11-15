barrett384:
  /* q2'' = q2' >> 384 = [w20, w19] = [w18, w17, w16] >> 384
                                    = [w18, w17] >> 128 */
  bn.rshi w20, w18, w31 >> 128
  bn.rshi w19, w17, w18 >> 128
  /* Add q1. This is unconditional since MSb of u is always 1.
     This cannot overflow due to leading zeros.
     q2''' = q2'' + q1 = [w20, w19] = [w20, w19] + [w8, w9] */
  bn.add w19, w19, w8
  bn.addc w20, w20, w9
  /* Conditionally add u (without leading 1) in case of MSb of x being set.
     This is the "real" q2 but shifted by 384 bits to the right. This cannot
     overflow due to leading zeros
     q2'''' = x[767]?q2'''+u[383:0]:q2'''
            = [w20, w19] + [w25, w24] = q2 >> 384 */
  bn.add w19, w19, w24
  bn.addc w20, w20, w25
  /* finally this gives q3 by shifting the remain bit to the right
     q3 = q2 >> 385 = q2'''' >> 1 = [w9, w8] = [w20, w19] >> 1 */
  bn.rshi w9, w20, w31 >> 1
  bn.rshi w8, w19, w20 >> 1