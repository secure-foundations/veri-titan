include "nth_root.dfy"
include "ntt_index.dfy"
include "polys.dfy"

module twiddle_factors {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2

    import opened nth_root
    import opened ntt_index
    import opened ntt_polys

    type n_sized = s: seq<elem>
        | |s| == N == pow2(LOGN).full witness *

    function A(): seq<elem>
        ensures |A()| == N == pow2(LOGN).full;

    function method block_count(m: pow2_t): pow2_t
        requires 0 <= m.exp <= LOGN;
    {
        pow2_div(pow2(LOGN), m)
    }

    function method block_size(c: pow2_t): pow2_t
        requires 0 <= c.exp <= LOGN;
    {
        pow2_div(pow2(LOGN), c)
    }

    lemma block_count_product_lemma(m: pow2_t)
        requires 0 <= m.exp <= LOGN;
        ensures block_count(m).full * m.full == N;
    {
        Nth_root_lemma();
    }

    lemma block_count_half_lemma(m: pow2_t)
        requires 1 <= m.exp <= LOGN;
        ensures block_count(pow2_half(m)) == pow2_double(block_count(m));
    {
        Nth_root_lemma();
        var left := pow2_div(pow2(LOGN), pow2_half(m));
        assert left.full * (m.full / 2) == N;
        var right := pow2_div(pow2(LOGN), m);
        var half := m.full / 2;
        pow2_basics(m);

        calc == {
            left.full * half;
            left.full * (m.full / 2);
            right.full * (2 * half);
            {
                LemmaMulIsAssociativeAuto();
            }
            (right.full * 2) * half;
        }
        LemmaMulEqualityConverse(half, left.full, right.full * 2);
    }

    // d is the block count
    // i is the offset in the block
    function method x_value(i: nat, d: pow2_t): (r: elem)
        requires d.exp <= LOGN;
        requires i < block_size(d).full;
        ensures r > 0;
    {
        var bound := block_size(d);
        LemmaMulNonnegative(2 * bit_rev_int(i, bound), d.full);
        var r := modpow(PSI, 2 * bit_rev_int(i, bound) * d.full + d.full);
        // LemmaPowPositive(PSI, 2 * bit_rev_int(i, bound) * d.full + d.full);
        calc {
            2 * bit_rev_int(i, bound) * d.full + d.full;
            {
                LemmaMulProperties();
            }
            (bit_rev_int(i, bound) * (2 * d.full)) + d.full;
            <=
            {
                LemmaMulInequality(bit_rev_int(i, bound), bound.full - 1, 2 * d.full);
            }
            (bound.full - 1) * (2 * d.full) + d.full;
            {
                LemmaMulIsDistributive(2 * d.full, bound.full, - 1);
            }
            bound.full * (2 * d.full) - (2 * d.full) + d.full;
            bound.full * (2 * d.full) - d.full;
            {
                LemmaMulProperties();
            }
            2 * (bound.full * d.full) - d.full;
            {
                block_count_product_lemma(bound);
            }
            2 * N - d.full;
        }
        primitive_root_lemma(2 * bit_rev_int(i, bound) * d.full + d.full);
        r
    }

    lemma twiddle_factors_index_bound_lemma(t: pow2_t, j: nat)
        returns (d: pow2_t)
        requires t.exp < LOGN;
        requires j < t.full;
        ensures t.full + j < N;
        ensures d == pow2_half(block_count(t));
        ensures 2 * j < block_size(d).full;
    {
        assert t.full <= N / 2 by {
            reveal Pow2();
            LemmaPowIncreases(2, t.exp, LOGN-1);
            Nth_root_lemma();
            assert pow2(LOGN-1) == pow2_half(pow2(LOGN));
            assert pow2(LOGN-1).full == N / 2;
        }
        calc {
            t.full + j;
            <
            2 * t.full;
            <=
            2 * (N / 2); 
            N;
        }

        d := block_count(t);
        assert block_size(d) == t;

        calc {
            2 * j;
            <
            2 * t.full;
            2 * block_size(d).full;
            pow2_double(block_size(d)).full;
            {
                block_count_half_lemma(d);
            }
            block_size(pow2_half(d)).full;
        }

        d := pow2_half(block_count(t));
    }

    function P(): seq<elem>
        ensures |P()| == N == pow2(LOGN).full;

    lemma {:axiom} twiddle_factors_value_axiom(t: pow2_t, d: pow2_t, j: nat)
        requires t.exp < LOGN;
        requires j < t.full;
        requires t.full + j < N;
        requires d == pow2_half(block_count(t));
        requires 2 * j < block_size(d).full;
        ensures P()[t.full + j] ==
            modmul(x_value(2 * j, d), R);

    lemma twiddle_factors_value_lemma(t: pow2_t, d: pow2_t, j: nat)
        requires t.exp < LOGN;
        requires j < t.full;
        requires d == pow2_half(block_count(t));
        ensures t.full + j < N;
        ensures 2 * j < block_size(d).full;
        ensures P()[t.full + j] ==
            modmul(x_value(2 * j, d), R);
    {
        var _ := twiddle_factors_index_bound_lemma(t, j);
        // P()[t.full + j] == modmul(x_value(2 * j, d), R);
        twiddle_factors_value_axiom(t, d, j);
    }
}
