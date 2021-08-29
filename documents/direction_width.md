# Width Independent Proofs

There are many places where certain theorem holds, regardless of the width of the bit vectors invloved. It is easy to thoroughly check small width examples, while difficult to do so for large with bit vectors. If we can somehow generate a proof from the smaller example to a larger one, or prove a theorem is width independent, then we can save a lot of effors.

## Polynomial Encoding Of BV (Inductive):

Here the idea is to encode the bit-vector operations using polynomials, then try to automate the proofs using algebra solvers.
We are dealing with variable number of bits (bit width independent), but we can't unfold the recursive definitions infinite number of times (or can we just unfold it 256 times while still being scalable?). Instead we attempt to automate the inductive proof, since the single bit (and/or/xor) gates can be represented using polynomials.

In the following `*`, `+` are used as mathematical multiplication and addition with no wrapping. `bv_add(x, y, n)` is used as `n bits` bit vector add with wrapping.


assume `x'`	and `y'` are `n + 1` bits BVs, extended from `x` and `y`, then we can write the definition inductively:

		x' - pow2(n) * b0 - x == 0
		y' - pow2(n) * b1 - y == 0

make sure `b0`, `b1` are single bit:

		b0 * (1 - b0) == 0
		b1 * (1 - b1) == 0

## Polynomial Encoding of And (Inductive):

		bv_and(x', y', n + 1) == pow2(n) * bv_and(b0, b1, 1) + bv_and(x, y, n)

introduce a single bit variable so that `t == b0 & b1`:

		bv_and(x', y', n + 1) - pow2(n) * t - bv_and(x, y, n) == 0

		t * (1 - t) == 0
		t - b0 * b1 == 0

## Polynomial Encoding of Or (Inductive):

		bv_or(x', y', n + 1) == pow2(n) * bv_or(b0, b1, 1) + bv_or(x, y, n)

introduce a single bit variable so that `t == b0 | b1`:

		bv_or(x', y', n + 1) - pow2(n) * t + bv_or(x, y, n)

		t * (1 - t) == 0
		(1 - t) - (1 + b0 * b1 - b0 - b1) == 0

## Polynomial Encoding of Add (Non-Inductive):

		bv_add(x', y', n + 1) == (x' + y') % pow2(n + 1)

there exists `k` such that the following holds:

		bv_add(x', y', n + 1) - x' - y' - k * pow2(n + 1) == 0

## Polynomial Encoding of Add (Inductive):

		TBD

## Polynomial Encoding of Mul (Non-Inductive):

		bv_mul(x', y', n + 1) == (x' * y') % pow2(n + 1)

there exists `k` such that the following holds:

		bv_mul(x', y', n + 1) - x' * y' - k * pow2(n + 1) == 0

## Polynomial Encoding of Mul (Inductive):

		TBD

## A Very Simple Lemma:

		x' & y' == y' & x'

### Base Case:

		TBD

### Inductive Case:

given: `bv_and(x, y, n) == bv_and(y, x, n)`

show: `bv_and(x', y', n + 1) == bv_and(y', x', n + 1)`

we derive the following equations:

use our encoding above for `bv_and`, define the relationship between `bv_and(x', y', n)` and `bv_and(x, y, n)`:

		bv_and(x', y', n + 1) - pow2(n) * t1 - bv_and(x, y, n) == 0
		t1 * (1 - t1) == 0
		t1 - b0 * b1 == 0

use our encoding above for `bv_and`, define the relationship between `bv_and(y', x', n)` and `bv_and(y, x, n)`:

		bv_and(y', x', n + 1) - pow2(n) * t2 - bv_and(y, x, n) == 0

		t2 * (1 - t2) == 0
		t2 - b1 * b0 == 0

finally add the induction hypothesis:

		bv_and(x, y, n) - bv_and(y, x, n) == 0

all together, we define this set of polynomials `P`:

		x' - pow2(n) * b0 - x
		y' - pow2(n) * b1 - y

		b0 * (1 - b0)
		b1 * (1 - b1)

		bv_and(x', y', n + 1) - pow2(n) * t1 - bv_and(x, y, n)

		t1 * (1 - t1)
		t1 - b0 * b1

		bv_and(y', x', n + 1) - pow2(n) * t2 - bv_and(y, x, n)

		t2 * (1 - t2)
		t2 - b1 * b0

		bv_and(x, y, n) - bv_and(y, x, n)

the goal can be translated into `g`:

		bv_and(x', y', n + 1) - bv_and(y', x', n + 1)

now we have finished the polynomial encoding. 

We then ask is `g` is included in the ring ideal constructed by `P`? If so, then `g` can be written as a linear combination of the polynomials in `P`. Since all the polynomials in `P` are effectively 0, `g` must also be 0, 
then we have a proof. If not then its very unfortunate. 

<!-- ## A Slightly More Complicated Lemma -->


## MULQACC examples

We need to write a bunch of proofs on multiplication with `BN.MULQACC`, which is an instruction that takes in two registers, multiply selected quarter words from each register, shift the product by some amount, add the shifted result to the wacc accumulator register. For example:
```
BN.MULQACC        w0.0, w1.3, 2
```
reads from the `0` quarter word from `w0` and `3` quarter word from `w1` multiply them, shift the result by `2` quarter words (`128` bits), then add to the accumulator `wacc`. The final addition is bit vector addition, so it cuts off after `256` bits:
```
wacc = (wacc + w0.0 * w1.3 * 2 ** 128) % 2 ** 256
```

`BN.MULQACC` can be chained together to perform longer multiplication. Here is a toy example where we compute the `256` bit product of the lower `128` bits of  `w28` and `w29`.

```
BN.MULQACC.Z      w28.0, w29.0, 0
BN.MULQACC        w28.1, w29.0, 1
BN.MULQACC        w28.0, w29.1, 1
BN.MULQACC        w28.1, w29.1, 2
```

## algebraic encoding and why it doesn't work directly

What makes it tricky to use algebraic solver on that directly is the bit vector addition, which might or might not overflow. We can introduce some unconstrained boolean variables, which indicates the overflow bit. 

```
ring r=integer,(w28, w28_h0, w28_h1, w28_q0, w28_q1, w28_q2, w28_q3,
    w29, w29_h0, w29_h1, w29_q0, w29_q1, w29_q2, w29_q3,
    wacc_g1, wacc_g2, wacc_g3, wacc_g4, B, k_0, k_1, k_2),lp;

ideal I =
    w28 - w28_h0 - w28_h1 * B^2, // w28 is made of two half words
    w28_h0 - w28_q0 - w28_q1 * B, // lower half word is made of two quarter words
    w28_h1 - w28_q2 - w28_q3 * B,  // higher half word is made of two quarter words

    w29 - w29_h0 - w29_h1 * B^2, // same deal in w29
    w29_h0 - w29_q0 - w29_q1 * B,
    w29_h1 - w29_q2 - w29_q3 * B,

    wacc_g1 - w28_q0 * w29_q0, // MULQACC.Z, which clears the initial wacc
    wacc_g2 - wacc_g1 - w28_q1 * w29_q0 * B - k_0 * B^4, // since we don't know if overflow happened or not, we put k_0 here
    wacc_g3 - wacc_g2 - w28_q0 * w29_q1 * B - k_1 * B^4,
    wacc_g4 - wacc_g3 - w28_q1 * w29_q1 * B^2 - k_2 * B^4,

    k_0 * (k_0 - 1), // the overflow bits
    k_1 * (k_1 - 1),
    k_2 * (k_2 - 1);

ideal G = groebner(I);
reduce(wacc_g4 - w28_h0 * w29_h0, G);
```

Not very surprisingly, `Singular` cannot reduce `wacc_g4 - w28_h0 * w29_h0` to `0`, instead it gives:

```
B^4*k_0+B^4*k_1+B^4*k_2
```
We note that
* For some small `B`, for example `B = 1`, we can confirm the term is `0` by exhaustively checking, which means `k_i` are all `0`. Sadly the implication does not work the other way around, we can't tell if `k_i` are all `0` when `B!=1`.
* This makes the proof obligations more explicit. Since  `B != 0`, to show the term reduces `0`, we need to show that `k_i` are all `0`. 
