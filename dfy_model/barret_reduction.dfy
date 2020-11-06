include "NativeTypes.dfy"
include "BitVector.dfy"
include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

module barret384 {
    import opened NativeTypes
    import opened powers
    import opened congruences
    import opened CutomBitVector

    method mul_384_384_768(a: cbv384, b: cbv384) returns (c: cbv768)
        ensures to_nat(c) == to_nat(a) * to_nat(b);
    {
        assume false;
    }

    /*
    * @param[in] [w9, w8]: a, first operand, max. length 384 bit.
    * @param[in] [w11, w10]: b, second operand, max. length 384 bit.
    * @param[in] [w13, w12]: m, modulus, max. length 384 bit, 2^384 > m > 2^383.
    * @param[in] [w15, w14]: u, pre-computed Barrett constant (without u[384]/MSb
    *                           of u which is always 1 for the allowed range but
    *                           has to be set to 0 here).
    * @param[in] w31: all-zero.
    */
    method barret384(
        a: cbv384,
        b: cbv384,
        m: cbv384,
        u: cbv384)
    {
        var x: cbv768 := mul_384_384_768(a, b);

        var msb := msb(x);

        var t: cbv384;
        if msb == 1 {
        	t := u;
        } else {
            t := cbv_zero(384);
        }

        var r1: cbv385 := cbv_slice(x, 0, 385);

        var q1: cbv385 := cbv_lsr(x, 383);

        var q1': cbv384 := cbv_slice(q1, 0, 384);
        var q2': cbv768 := mul_384_384_768(q1', u);

        var q2'': cbv384 := cbv_lsr(q2', 384);
        
        var q2''': cbv := cbv_add(q2'', q1);

        var q2'''' := cbv_add(q2''', t);
        var q3 := cbv_lsr(x, 383);
    }

    // lemma barrett_reduction_q3_bound(
    //     x: nat,
    //     m: nat,
    //     Q: nat,
    //     q3: nat,
    //     n: nat)

    //     requires n > 0;
    //     requires pow2(n - 1) <= m < pow2(n);
    //     requires 0 < x < pow2(2 * n);
    //     requires Q == x / m;
    //     requires q3 == ((x / pow2(n - 1)) * (pow2(2 * n) / m)) / pow2(n + 1);

    //     ensures Q - 2 <= q3 <= Q;
    // {
    //     var c0 := pow2(n - 1);
    //     var c1 := pow2(n + 1);
    //     var c2 := pow2(2 * n);

    //     var cr0 := pow2(n - 1) as real;
    //     var cr1 := pow2(n + 1) as real;
    //     var cr2 := pow2(2 * n) as real;

    //     var xr := x as real;
    //     var mr := m as real;

    //     var alpha : real := xr / cr0 - (x / c0) as real;
    //     var beta : real := cr2 / mr - (c2 / m) as real;

    //     calc <= {
    //         Q;
    //         x / m;
    //         {
    //             assume false;
    //         }
    //         (xr / mr).Floor;
    //         {
    //             calc <= {
    //                 xr / mr;
    //                 {
    //                     assume cr2 == cr0 * cr1;
    //                 }
    //                 ((xr / cr0) * (cr2 / mr)) / cr1;
    //                 (((x / c0) as real + alpha) * (cr2 / mr)) / cr1;
    //                 (((x / c0) as real + alpha) * ((c2 / m) as real + beta)) / cr1;
    //                 ((x / c0) as real * (c2 / m) as real + beta * (x / c0) as real + alpha * (c2 / m) as real + alpha * beta) / cr1;
    //                 {
    //                     assume 0.0 <= alpha < 1.0;
    //                     assume false; // should be true
    //                 }
    //                 ((x / c0) as real * (c2 / m) as real + beta * (x / c0) as real + (c2 / m) as real + beta) / cr1;
    //                 {
    //                     assume 0.0 <= beta < 1.0;
    //                     assume false; // should be true
    //                 }
    //                 ((x / c0) as real * (c2 / m) as real + (x / c0) as real + (c2 / m) as real + 1.0) / cr1;
    //                 {
    //                     assume (x / c0) as real <= cr1 - 1.0;
    //                     assume false; // unstable
    //                 }
    //                 ((x / c0) as real * (c2 / m) as real) / cr1 + (cr1 + (c2 / m) as real) / cr1;
    //                 {
    //                     assume (c2 / m) as real <= cr1;
    //                     assume false; // unstable
    //                 }
    //                 ((x / c0) as real * (c2 / m) as real) / cr1 + (cr1 + cr1) / cr1;
    //                 {
    //                     assume (cr1 + cr1) / cr1 == 2.0;
    //                 }
    //                 ((x / c0) as real * (c2 / m) as real) / cr1 + 2.0;
    //                 {
    //                     assert (x / c0) as real * (c2 / m) as real == ((x / c0) * (c2 / m)) as real;
    //                     assume false; // unstable
    //                 }
    //                 (((x / c0) * (c2 / m)) as real) / cr1 + 2.0;
    //             }
    //             assert xr / mr <= (((x / c0) * (c2 / m)) as real) / cr1 + 2.0;
    //         }
    //         ((((x / c0) * (c2 / m)) as real) / cr1 + 2.0).Floor;
    //         ((((x / c0) * (c2 / m)) as real) / cr1).Floor + 2.0.Floor;
    //         ((((x / c0) * (c2 / m)) as real) / cr1).Floor + 2;
    //         {
    //             assume (x / c0) * (c2 / m) != 0;
    //             floor_div_lemma((x / c0) * (c2 / m), c1);
    //         }
    //         ((x / c0) * (c2 / m)) / c1 + 2;
    //     }

    //     assert Q - 2 <= ((x / c0) * (c2 / m)) / c1;
    //     assume q3 <= Q;
    // }

    // method barrett_reduction(
    //     x: nat,
    //     m: nat,
    //     ghost Q: nat,
    //     ghost R: nat,
    //     q3: nat,
    //     n: nat)

    //     returns (r: int)

    //     requires n > 0;
    //     requires pow2(n - 1) <= m < pow2(n);
    //     requires 0 < x < pow2(2 * n);

    //     requires Q == x / m;
    //     requires R == x % m;
    //     requires Q - 2 <= q3 <= Q;

    //     ensures r == R;
    // {
    //     var c1 := pow2(n + 2);

    //     var r1 := x % c1;
    //     var r2 := (q3 * m) % c1;
    //     r := r1 as int - r2 as int;

    //     assert 0 - c1 as int < r < c1 as int;

    //     assert r % c1 == (Q - q3) * m + R by {
    //         calc == {
    //             r % c1;
    //             ((x % c1) - (q3 * m) % c1) % c1;
    //             {
    //                 assume false;
    //             }
    //             (x - q3 * m) % c1;
    //             {
    //                 assert x == Q * m + R;
    //             }
    //             ((Q - q3) * m + R) % c1;
    //             {
    //                 var t := (Q - q3) * m + R;
    //                 assume 0 <= t < 3 * m;
    //                 assume 3 * m < c1;
    //                 remainder_unqiue_lemma(t, c1);
    //             }
    //             (Q - q3) * m + R;
    //         }
    //     }

    //     if r < 0 {
    //         var r' := r + c1;
    //         assert 0 <= r' < c1;

    //         calc == {
    //             r';
    //             {
    //                 remainder_unqiue_lemma(r', c1);
    //             }
    //             r' % c1;
    //             {
    //                 assume r' % c1 == r % c1;
    //             }
    //             r % c1;
    //             (Q - q3) * m + R;
    //         }
    //         r := r';
    //     } else {
    //         calc == {
    //             r;
    //             {
    //                 remainder_unqiue_lemma(r, c1);
    //             }
    //             r % c1;
    //             (Q - q3) * m + R;
    //         }
    //     }

    //     assert r == (Q - q3) * m + R;
    //     assert r % m == R by {
    //         mod_factor_lemma(r, Q - q3, R, m);
    //     }
    //     sanity_check(Q, R, q3, r, m);

    //     if r >= m {
    //         assert r <= 2 * m + R;
    //         r := r - m;
    //         assert r <= m + R;

    //         assert r % m == R by {
    //             mod_factor_lemma(r, Q - q3 - 1, R, m);
    //         }
    //     }

    //     if r >= m {
    //         assert r <= m + R;
    //         r := r - m;
    //         assert r <= R;
    //         assert r < m;
    //         assume cong(r, R, m);

    //         assert r % m == R by {
    //             mod_factor_lemma(r, Q - q3 - 2, R, m);
    //         }
    //     }

    //     assert r % m == R;
    //     assert 0 <= r < m;
    //     assert r == R;
    // }

    // lemma sanity_check(Q: nat, R: nat, q3: nat, r: nat, m: nat)
    //     requires r == (Q - q3) * m + R;
    //     requires Q - 2 <= q3 <= Q;
    //     ensures R <= r <= 2 * m + R;
    // {
    //     // assert 0 <= Q - q3 <= 2;
    // }

    // lemma mod_factor_lemma(r: nat, k: int, R: nat, m: nat)
    //     requires r == k * m + R;
    //     requires m != 0;
    //     ensures r % m == R;
    // {
    //     assume false;
    // }

    // lemma remainder_unqiue_lemma(r: nat, m: nat)
    //     requires 0 <= r < m;
    //     ensures r % m == r;
    // {
    //     assert true;
    // }

    // lemma floor_div_lemma(x: nat, y: nat)
    //     requires 0 < x && 0 < y;
    //     ensures  x / y == (x as real / y as real).Floor;
    // {
    //     assume false;
    // }

    // lemma div_bound_lemma(x: nat, y: nat)
    //     requires 0 < x && 0 < y;
    //     // requires rq == (x as real) / (y as real);
    //     ensures (x as real) / (y as real) - 1.0 < (x / y) as real <= (x as real) / (y as real);
    // {
    //     var rq :real := (x as real) / (y as real);
    //     var q := x / y;

    //     var r := x % y;
    //     assert x == y * q + r;
    //     assert y * q == x - r;

    //     var f := r as real / y as real;
    //     assert f < 1.0;
    
    //     calc == {
    //         q as real;
    //         (x as real - r as real) / y as real;
    //         rq - r as real / y as real;
    //         rq - f;
    //     }

    //     assert q as real <= rq;
    //     assert q as real > rq - 1.0;
    // }
}