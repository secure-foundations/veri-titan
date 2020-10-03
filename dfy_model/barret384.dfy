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
        requires pow2(n - 1) < m < pow2(n);
        requires 0 < x < pow2(2 * n);
    {
        
    }

    lemma floor_div_lemma(x: nat, y: nat, q: nat, rq :real)
        requires 0 < x && 0 < y;
        requires q == x / y;
        requires rq == (x as real) / (y as real);
        ensures rq - 1.0 < q as real <= rq;
    {
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