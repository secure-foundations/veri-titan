	x' == pow2(n) * b0 + x
	y' == pow2(n) * b1 + y

### encoding of and:

    bv_and(x', y', n) == pow2(n) * bv_and(b0, b1, 1) + bv_and(x, y, n - 1)

introduce a single bit variable `t`:

	bv_and(x', y', n) - pow2(n) * t - bv_and(x, y, n - 1) == 0

	t - b0 * b1 == 0
	t * (1 - t) == 0
	b0 * (1 - b0) == 0
	b1 * (1 - b1) == 0

### encoding of add:

    bv_add(x', y', n) == (pow2(n) * (b0 + b1) + x + y) % pow2(n + 1)

this requires some tweaks, since we are talking about mod pow2(n + 1), there exists `k` such that the following holds:

    bv_add(x', y', n) - pow2(n) * (b0 + b1) - x - y - k * pow2(n + 1) == 0

    pow2(n + 1) - pow2(n) * 2 == 0
    b0 * (1 - b0) == 0
	b1 * (1 - b1) == 0

## trivial lemma:

	x' & y' == y' & x'

base case: can be exhaustively checked 

inductive case:

given:

    bv_and(x, y, n - 1) == bv_and(y, x, n - 1)

show:

    bv_and(x', y', n) == bv_and(y', x', n)

we derive the following equations:

make sure b0, b1 are single binary:

	b0 * (1 - b0) == 0
	b1 * (1 - b1) == 0

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



