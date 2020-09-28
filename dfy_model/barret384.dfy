include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

module barret384 {
    import opened NativeTypes
    import opened powers
    import opened congruences

    method barrett_reduction(x: nat, m: int, u: nat, b: nat, k: nat)
        requires b > 3;
        requires k > 0;

        requires power(b, k - 1) < m < power(b, k);
        requires 0 < x < power(b, 2 * k);
        requires u == power(b, 2 * k) / m;
    {
        // ghost var Q := x / m;
        // ghost var P := x % m;

        // var q1 := x / power(b, k - 1);
        // var q2 := q1 * u;
        // var q3 := q2 / power(b, k + 1);

        // if q3 > Q {
            // assert q3 * power(b, k + 1) > 
        // }
    }

    lemma floor_div_lemma(x: nat, y: nat)
        requires 0 < x && 0 < y;
    {
        var q := x / y;
        var r := x % y;
        assert x == y * q + r;
        assert y * q == x - r;

        var rq :real := (x as real) / (y as real);

        var f := r as real / y as real;
        assert f < 1.0;
    
        calc == {
            q as real;
            (x as real - r as real) / y as real;
            rq - r as real / y as real;
            rq - f;
        }

        assert q as real <= rq;
        assert q as real > rq - 1.0;
    }
}