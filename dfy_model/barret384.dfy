include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

module barret384 {
    import opened NativeTypes
    import opened powers
    import opened congruences

    function method pow2(n: nat) : nat
    {
        power(2, n)
    }

    lemma barrett_reduction_lemma(
        x: nat,
        xr: real,
        m: nat,
        mr: real,
        q: nat,
        n: nat)

        requires n > 0;
        requires x as real == xr;
        requires m as real == mr && m > 0;
        requires q == x / m;
        requires pow2(n - 1) <= m < pow2(n);
        requires 0 < x < pow2(2 * n);
    {
        var c0 := pow2(n - 1);
        var c1 := pow2(n + 1);
        var c2 := pow2(2 * n);

        var cr0 := pow2(n - 1) as real;
        var cr1 := pow2(n + 1) as real;
        var cr2 := pow2(2 * n) as real;

        // var qr : real := xr / mr;
        var alpha : real := xr / cr0 - (x / c0) as real;
        var beta : real := cr2 / mr - (c2 / m) as real;

        calc <= {
            q;
            x / m;
            {
                assume false;
            }
            (xr / mr).Floor;
            {
                assume cr2 == cr0 * cr1;
                assert ((xr / cr0) * (cr2 / mr)) / cr1 == xr / mr;
            }
            (((xr / cr0) * (cr2 / mr)) / cr1).Floor;
        }
        // assert 
    }

    lemma floor_div_lemma(x: nat, y: nat)
        requires 0 < x && 0 < y;
        // requires rq == (x as real) / (y as real);
        ensures (x as real) / (y as real) - 1.0 < (x / y) as real <= (x as real) / (y as real);
    {
        var rq :real := (x as real) / (y as real);
        var q := x / y;

        var r := x % y;
        assert x == y * q + r;
        assert y * q == x - r;

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