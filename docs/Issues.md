[otbn, sw] clarification on the RSA signature verification routine
----
I am wondering what the plan is on the RSA signature verification routine (used for secure boot process). `modexp.s` seems to be a general version that could handle variable key length. Is there going to be a version that tailors to the specific key length for the secure boot process? If so, how much difference would be expected? Thank you. 

[otbn, sw] assumptions of `barrett384.s`
----
We had a discussion with @felixmiller at some point, so this is more for the record. 

Using the terms from 14.42 in "Handbook of Applied Cryptography",  `b` is the radix, and `k` is some exponent. The book assumes that `b > 3`, so the inequality `(Q - q3) * m + R < 3 * m < b ^ (k + 1)` holds.

The current implementation of `barrett384` is using radix `b = 2`, and exponent `k = 384`. If we assume generally that `2^383 < m < 2^384`, then the inequality should not hold. 

However, as @felixmiller pointed out earlier, using the modulus of p384 and p256, it should be possible to show that `Q ≤ q3 ≤ Q + 1`. Then we can show that `(Q - q3) * m + R < 2 * m < b ^ (k + 1)` holds.

To summarize, the current barrett384.s should have this tighter bounded when working with particular modulus, but might need a fix for general modulus. My understanding is that there will be different versions for each. 

[otbn, sw] computation of `q3` in `barrett384.s`
----
Starting from [here](https://github.com/lowRISC/opentitan/blob/4a8eea22f7e4dbb6c986126970cf37e6903871c8/sw/otbn/code-snippets/barrett384.s#L167), in the first step:

```
  /* Add q1. This is unconditional since MSb of u is always 1.
     This cannot overflow due to leading zeros.
     q2''' = q2'' + q1 = [w20, w19] = [w20, w19] + [w8, w9] */
  bn.add w19, w19, w8
  bn.addc w20, w20, w9
```

`q1` is a 385 bit number from the previous step, and `q2''` is a 384 bit number, so `q2'''` could use 386 bits.

In the next step:

```
  /* Conditionally add u (without leading 1) in case of MSb of x being set.
     This is the "real" q2 but shifted by 384 bits to the right. This cannot
     overflow due to leading zeros
     q2'''' = x[767]?q2'''+u[383:0]:q2'''
            = [w20, w19] + [w25, w24] = q2 >> 384 */
  bn.add w19, w19, w24
  bn.addc w20, w20, w25
  ```
Another 384 bit number is "conditionally" added to `q2'''`. Therefore `q2''''` should still fit into 386 bits.

In the next step:
```
/* finally this gives q3 by shifting the remain bit to the right
	q3 = q2 >> 385 = q2'''' >> 1 = [w9, w8] = [w20, w19] >> 1 */
bn.rshi w9, w20, w31 >> 1
bn.rshi w8, w19, w20 >> 1
```
`q2'''' ` is right shifted to compute `q3`, so `q3 = [w9, w8]` should fit into 385 bits. 

In the next step:
```
/* Compute r2 = q3 * m % 2^385.
	=> max. length r2: 385 bit
	q3*m = [w18, w17, w16] = [w9, w8] * [w13,w12] */
bn.mov w10, w12
bn.mov w11, w13
jal x1, mul384
```
The multiplication works for 384 bits numbers. However `q3` is 385 bits. Let `b` be the most significant bit of `q3` and `q3'` be the rest of the 384 bits. So `q3 = b * 2^384 + q3'`. So it seem like that the multiplication computes `q3' * m`, instead of  `q3 * m`.  We note that `r` only cares about `q3 * m % 2^385`, so we check:
```
q3 * m % 2^385 
= (b * 2^384 + q3') * m % 2^385
= (b * 2^384 * m + q3' * m) % 2^385
```
So it seems like when `b = 1`, unless `m` (which is the modulo) is even, the remainders are not equal. 
