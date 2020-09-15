## Setup:

assume `x'`	and `y'` are `n` bits BVs, extended from `x` and `y`, then we can write the definition inductively:

	x' - pow2(n) * b0 - x == 0
	y' - pow2(n) * b1 - y == 0

make sure b0, b1 are single bit:

	b0 * (1 - b0) == 0
	b1 * (1 - b1) == 0

## Polynomial Encoding of And:

    bv_and(x', y', n) == pow2(n) * bv_and(b0, b1, 1) + bv_and(x, y, n - 1)

introduce a single bit variable `t == b0 & b1`:

	bv_and(x', y', n) - pow2(n) * t - bv_and(x, y, n - 1) == 0

	t * (1 - t) == 0
	t - b0 * b1 == 0

## Polynomial Encoding of Or:

    bv_or(x', y', n) == pow2(n) * bv_or(b0, b1, 1) + bv_or(x, y, n - 1)

introduce a single bit variable `t == b0 | b1`:

    bv_or(x', y', n) - pow2(n) * t + bv_or(x, y, n - 1)

	t * (1 - t) == 0
	(1 - t) - (1 + b0 * b1 - b0 - b1) == 0

## Polynomial Encoding of Add:

    bv_add(x', y', n) == (x' + y') % pow2(n + 1)

there exists `k` such that the following holds:

    bv_add(x', y', n) - x' - y' - k * pow2(n + 1) == 0

## Polynomial Encoding of Mul:

    bv_mul(x', y', n) == (x' * y') % pow2(n + 1)

there exists `k` such that the following holds:

    bv_mul(x', y', n) - x' * y' - k * pow2(n + 1) == 0

## lemma1:

	x' & y' == y' & x'

base case: can be exhaustively checked 

inductive case:

given:

    bv_and(x, y, n - 1) == bv_and(y, x, n - 1)

show:

    bv_and(x', y', n) == bv_and(y', x', n)

we derive the following equations:

make sure t1 is binary, and `t1 == b0 & b1`:

	t1 * (1 - t1) == 0
	t1 - b0 * b1 == 0

define the relationship between `bv_and(x', y', n)` and `bv_and(x, y, n)`:

	bv_and(x', y', n) - pow2(n) * t1 - bv_and(x, y, n - 1) == 0

make sure t2 is binary, and `t2 == b1 & b0`:

	t2 * (1 - t2) == 0
	t2 - b1 * b0 == 0

define the relationship between `bv_and(y', x', n)` and `bv_and(y, x, n)`:

	bv_and(y', x', n) - pow2(n) * t2 - bv_and(y, x, n - 1) == 0

finally add the induction hypothesis:

	bv_and(x, y, n - 1) - bv_and(y, x, n - 1) == 0

the goal can be translated into:

	bv_and(x', y', n) - bv_and(y', x', n) 

now we have finished the polynomial encoding of the problem.
we ask is this in the ring ideal constructed by the above equations include the goal? if so, then we have an inductive proof. if not, too bad.



