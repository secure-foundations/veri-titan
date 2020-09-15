The overall idea is to encode the bit-vector operations using polynomials, then try to automate the proofs using algebra solvers.
We are dealing with variable number of bits (bit width independent), but we can't unfold the recursive definitions infinite number of times (or can we just unfold it 256 times while still being scalable?). Instead we attempt to automate the inductive proof, since the single bit (and/or/xor) gates can be represented using polynomials.

In the following `*`, `+` are used as mathematical multiplication and addition with no wrapping. `bv_add(x, y, n)` is used as `n bits` bit vector add with wrapping.

## Polynomial Encoding Of BV (Inductive):

assume `x'`	and `y'` are `n` bits BVs, extended from `x` and `y`, then we can write the definition inductively:

		x' - pow2(n) * b0 - x == 0
		y' - pow2(n) * b1 - y == 0

make sure `b0`, `b1` are single bit:

		b0 * (1 - b0) == 0
		b1 * (1 - b1) == 0

## Polynomial Encoding of And (Inductive):

		bv_and(x', y', n) == pow2(n) * bv_and(b0, b1, 1) + bv_and(x, y, n - 1)

introduce a single bit variable so that `t == b0 & b1`:

		bv_and(x', y', n) - pow2(n) * t - bv_and(x, y, n - 1) == 0

		t * (1 - t) == 0
		t - b0 * b1 == 0

## Polynomial Encoding of Or (Inductive):

		bv_or(x', y', n) == pow2(n) * bv_or(b0, b1, 1) + bv_or(x, y, n - 1)

introduce a single bit variable so that `t == b0 | b1`:

		bv_or(x', y', n) - pow2(n) * t + bv_or(x, y, n - 1)

		t * (1 - t) == 0
		(1 - t) - (1 + b0 * b1 - b0 - b1) == 0

## Polynomial Encoding of Add (Non-Inductive):

		bv_add(x', y', n) == (x' + y') % pow2(n + 1)

there exists `k` such that the following holds:

		bv_add(x', y', n) - x' - y' - k * pow2(n + 1) == 0

## Polynomial Encoding of Add (Inductive):

		TBD

## Polynomial Encoding of Mul (Non-Inductive):

		bv_mul(x', y', n) == (x' * y') % pow2(n + 1)

there exists `k` such that the following holds:

		bv_mul(x', y', n) - x' * y' - k * pow2(n + 1) == 0

## Polynomial Encoding of Mul (Inductive):

		TBD

## A Very Simple Lemma:

		x' & y' == y' & x'

### Base Case:

		TBD

### Inductive Case:

given: `bv_and(x, y, n - 1) == bv_and(y, x, n - 1)`

show: `bv_and(x', y', n) == bv_and(y', x', n)`

we derive the following equations:

use our encoding above for `bv_and`, define the relationship between `bv_and(x', y', n)` and `bv_and(x, y, n)`:

		bv_and(x', y', n) - pow2(n) * t1 - bv_and(x, y, n - 1) == 0
		t1 * (1 - t1) == 0
		t1 - b0 * b1 == 0

use our encoding above for `bv_and`, define the relationship between `bv_and(y', x', n)` and `bv_and(y, x, n)`:

		bv_and(y', x', n) - pow2(n) * t2 - bv_and(y, x, n - 1) == 0

		t2 * (1 - t2) == 0
		t2 - b1 * b0 == 0

finally add the induction hypothesis:

		bv_and(x, y, n - 1) - bv_and(y, x, n - 1) == 0

all together, we define this set of polynomials `P`:

		x' - pow2(n) * b0 - x
		y' - pow2(n) * b1 - y

		b0 * (1 - b0)
		b1 * (1 - b1)

		bv_and(x', y', n) - pow2(n) * t1 - bv_and(x, y, n - 1)

		t1 * (1 - t1)
		t1 - b0 * b1

		bv_and(y', x', n) - pow2(n) * t2 - bv_and(y, x, n - 1)

		t2 * (1 - t2)
		t2 - b1 * b0

		bv_and(x, y, n - 1) - bv_and(y, x, n - 1)

the goal can be translated into `g`:

		bv_and(x', y', n) - bv_and(y', x', n) 

now we have finished the polynomial encoding. 

We then ask is `g` is included in the ring ideal constructed by `P`? If so, then `g` can be written as a linear combination of the polynomials in `P`. Since all the polynomials in `P` are effectively 0, `g` must also be 0, 
then we have a proof. If not then its very unfortunate. 

<!-- ## A Slightly More Complicated Lemma -->