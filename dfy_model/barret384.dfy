include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

module barret384 {
    import opened NativeTypes
    import opened powers
    import opened congruences

    method barrett_reduction(x: nat, m: int, u: nat, b: nat, k: nat)
        requires b > 3;
        requires 0 < m < power(b, k);
        requires 0 < x < power(b, 2 * k);
        requires k > 0;
        requires u == power(b, 2 * k) / m;
    {
        ghost var Q := x / m;
        ghost var P := x % m;

        var q1 := x / power(b, k - 1);
        // assert x - power(b, k - 1) < x * q1 <= x;
        var q2 := q1 * u;
        var q3 := q2 / power(b, k + 1);

        // if q3 > Q {
            // assert q3 * power(b, k + 1) > 
        // }
    }

    lemma floor_lemma(x: nat, y: nat, q: nat, r : nat)
        requires 0 < x && 0 < y;
        requires q == x / y;
        requires r == x % y;
    {
        assert r < y;
        assert x == q * y + r;
        assert x - r <= y * q <= x;
    }
}