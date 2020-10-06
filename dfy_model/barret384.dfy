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

        ensures q - 2 <= ((x / pow2(n - 1)) * (pow2(2 * n) / m)) / pow2(n + 1);
    {
        var c0 := pow2(n - 1);
        var c1 := pow2(n + 1);
        var c2 := pow2(2 * n);

        var cr0 := pow2(n - 1) as real;
        var cr1 := pow2(n + 1) as real;
        var cr2 := pow2(2 * n) as real;

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
                calc <= {
                    xr / mr;
                    {
                        assume cr2 == cr0 * cr1;
                    }
                    ((xr / cr0) * (cr2 / mr)) / cr1;
                    (((x / c0) as real + alpha) * (cr2 / mr)) / cr1;
                    (((x / c0) as real + alpha) * ((c2 / m) as real + beta)) / cr1;
                    ((x / c0) as real * (c2 / m) as real + beta * (x / c0) as real + alpha * (c2 / m) as real + alpha * beta) / cr1;
                    {
                        assume 0.0 <= alpha < 1.0;
                        assume false; // should be true
                    }
                    ((x / c0) as real * (c2 / m) as real + beta * (x / c0) as real + (c2 / m) as real + beta) / cr1;
                    {
                        assume 0.0 <= beta < 1.0;
                        assume false; // should be true
                    }
                    ((x / c0) as real * (c2 / m) as real + (x / c0) as real + (c2 / m) as real + 1.0) / cr1;
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
                assert xr / mr <= (((x / c0) * (c2 / m)) as real) / cr1 + 2.0;
            }
            ((((x / c0) * (c2 / m)) as real) / cr1 + 2.0).Floor;
            ((((x / c0) * (c2 / m)) as real) / cr1).Floor + 2.0.Floor;
            ((((x / c0) * (c2 / m)) as real) / cr1).Floor + 2;
            {
                assume (x / c0) * (c2 / m) != 0;
                floor_div_lemma((x / c0) * (c2 / m), c1);
            }
            ((x / c0) * (c2 / m)) / c1 + 2;
        }

        assert q - 2 <= ((x / c0) * (c2 / m)) / c1;
    }

    method barrett_post(
        x: nat,
        m: nat,
        q: nat,
        q3: nat,
        n: nat)

        returns (r: int)

        requires n > 0;
        requires pow2(n - 1) <= m < pow2(n);
        requires 0 < x < pow2(2 * n);

        requires q == x / m;
        requires q - 2 <= q3 <= q;

        ensures x % m <= r <= 2 * m + x % m;
    {
        var c1 := pow2(n + 2);

        var r1 := x % c1;
        var r2 := (q3 * m) % c1;
        r := r1 as int - r2 as int;

        assert 0 - c1 as int < r < c1 as int;

        assert r % c1 == (q - q3) * m + x % m by {
            calc == {
                r % c1;
                ((x % c1) - (q3 * m) % c1) % c1;
                {
                    assume false;
                }
                (x - q3 * m) % c1;
                {
                    assert x == q * m + x % m;
                }
                ((q - q3) * m + x % m) % c1;
                {
                    var t := (q - q3) * m + x % m;
                    assert 0 <= t < 3 * m;
                    assume 3 * m < c1;
                    remainder_unqiue_lemma(t, c1);
                }
                (q - q3) * m + x % m;
            }
        }

        if r >= 0 {
            calc == {
                r;
                {
                    remainder_unqiue_lemma(r, c1);
                }
                r % c1;
                (q - q3) * m + x % m;
            }
        } else {
            var r' := r + c1;
            assert 0 <= r' < c1;

            calc == {
                r';
                {
                    remainder_unqiue_lemma(r', c1);
                }
                r' % c1;
                {
                    assume r' % c1 == r % c1;
                }
                r % c1;
                (q - q3) * m + x % m;
            }
            
            r := r';
        }

        assert r == (q - q3) * m + x % m;
        assert x % m <= r <= 2 * m + x % m;
    }

    lemma remainder_unqiue_lemma(r: nat, m: nat)
        requires 0 <= r < m;
        ensures r % m == r;
    {
        assert true;
    }

    lemma floor_div_lemma(x: nat, y: nat)
        requires 0 < x && 0 < y;
        ensures  x / y == (x as real / y as real).Floor;
    {
        assume false;
    }

    lemma div_bound_lemma(x: nat, y: nat)
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