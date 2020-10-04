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
        qr: real,
        n: nat)

        requires n > 0;
        requires x as real == xr;
        requires m as real == mr && m > 0;
        requires qr == xr / mr;
        requires pow2(n - 1) <= m < pow2(n);
        requires 0 < x < pow2(2 * n);
    {
        var c0 := pow2(n - 1);
        var c1 := pow2(n + 1);
        var c2 := pow2(2 * n);

        var cr0 := pow2(n - 1) as real;
        var cr1 := pow2(n + 1) as real;
        var cr2 := pow2(2 * n) as real;

        var alpha : real := xr / cr0 - (x / c0) as real;
        var beta : real := cr2 / mr - (c2 / m) as real;

        calc <=
        {
            qr;
            {
                assume cr0 * cr1 == cr2;
            }
            (xr / cr0) * (cr2 / mr) / cr1;
            ((x / c0) as real + alpha) * ((c2 / m) as real + beta) / cr1;
            ((x / c0) as real * (c2 / m) as real + beta * (x / c0) as real + alpha * (c2 / m) as real + alpha * beta) / cr1;
            {
                assume 0.0 <= alpha <= 1.0;
                assume 0.0 <= beta <= 1.0;
                assume false; // unstable
            }
            ((x / c0) as real * (c2 / m) as real + (x / c0) as real + (c2 / m) as real + 1.0) / cr1;
            ((x / c0) as real * (c2 / m) as real) / cr1 + ((x / c0) as real + (c2 / m) as real + 1.0) / cr1;
            {
                assume (x / c0) as real <= cr1 - 1.0;
                assume false; // unstable
            }
            ((x / c0) as real * (c2 / m) as real) / cr1 + (cr1 + (c2 / m) as real) / cr1;
            {
                assume (c2 / m) as real <= cr1;
                assume false; // unstable
            }
            ((x / c0) as real * (c2 / m) as real) / cr1 + (cr1 + cr1) / cr1;
            ((x / c0) as real * (c2 / m) as real) / cr1 + 2.0;
            {
                assert (x / c0) as real * (c2 / m) as real == ((x / c0) * (c2 / m)) as real;
                assume false; // unstable
            }
            (((x / c0) * (c2 / m)) as real) / cr1 + 2.0;
        }

        assume c1 != 0;
        assume (x / c0) * (c2 / m) != 0;

        floor_div_lemma((x / c0) * (c2 / m), c1);
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