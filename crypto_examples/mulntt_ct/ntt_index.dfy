include "nth_root.dfy"
include "bins.dfy"
include "../ntt_cleanup/pow2.dfy"

module ntt_index {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened nth_root
    import opened pows_of_2
    import opened bins

    function method {:opaque} even_indexed_items<T>(a: seq<T>, len: pow2_t): seq<T>
        requires |a| == len.full;
    {
        pow2_basics(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2])
    }

    function method {:opaque} odd_indexed_items<T>(a: seq<T>, len: pow2_t): seq<T>
        requires |a| == len.full;
    {
        pow2_basics(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2 + 1])
    }

    function method {:opaque} merge_even_odd_indexed_items<T>(a: seq<T>, b: seq<T>, len: pow2_t): (r: seq<T>)
        requires |a| == |b| == len.full;
        ensures |r| == pow2_double(len).full;
        ensures even_indexed_items(r, pow2_double(len)) == a;
        ensures odd_indexed_items(r, pow2_double(len)) == b;
    {
        pow2_basics(len);
        var new_len := pow2_double(len);
        var r := seq(new_len.full, n requires 0 <= n < new_len.full => 
            if n % 2 == 0 then a[n/2] else b[n/2]);
        assert even_indexed_items(r, new_len) == a by {
            reveal even_indexed_items();
        }
        assert odd_indexed_items(r, new_len) == b by {
            reveal odd_indexed_items();
        }
        r
    }

    function method bit_rev_int(i: nat, bound: pow2_t): (ri: nat)
        requires i < bound.full;
        ensures ri < bound.full;
    {
        if bound.exp == 0 then
            i
        else
            reveal Pow2();
            var rs := Reverse(FromNatWithLen(i, bound.exp));
            LemmaSeqNatBound(rs);
            ToNatRight(rs)
    }

    lemma bit_rev_int_lemma0(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(i, pow2_double(bound)) == 2 * bit_rev_int(i, bound);
    {
        var dbound := pow2_double(bound);
        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(i, dbound.exp);
        var normal := FromNat(i);

        assert bdis[bound.exp] == 0 && bdis[..bound.exp] == bis by {
            BitSelModEquivalence(bdis, bound.exp);
            LemmaFundamentalDivModConverse(i, bound.full, 0, i);

            assert ToNatLeft(bdis) == ToNatLeft(bdis[..bound.exp]) by {
                reveal ToNatLeft();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[..bound.exp]);
            LemmaSeqEq(bdis[..bound.exp], bis);
        }

        calc == {
            bit_rev_int(i, dbound);
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == [0] + Reverse(bdis[..bound.exp]);
            }
            ToNatRight([0] + Reverse(bdis[..bound.exp]));
            ToNatRight([0] + Reverse(bis));
            {
                reveal ToNatRight();
            }
            2 * ToNatRight(Reverse(bis));
            2 * bit_rev_int(i, bound);
        }
    }

    lemma bit_rev_int_lemma1(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(i+bound.full, pow2_double(bound)) == 2 * bit_rev_int(i, bound) + 1;
    {
        var j := i+bound.full;
        var dbound := pow2_double(bound);
        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(j, dbound.exp);
        var normal := FromNat(j);

       assert bdis[bound.exp] == 1 && bdis[..bound.exp] == bis by {
            BitSelModEquivalence(bdis, bound.exp);
            LemmaFundamentalDivModConverse(j, bound.full, 1, i);

            assert ToNatLeft(bdis) == ToNatLeft(bdis[..bound.exp]) + bound.full by {
                reveal ToNatLeft();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[..bound.exp]);
            LemmaSeqEq(bdis[..bound.exp], bis);
        }

        calc == {
            bit_rev_int(j, dbound);
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == [1] + Reverse(bdis[..bound.exp]);
            }
            ToNatRight([1] + Reverse(bdis[..bound.exp]));
            ToNatRight([1] + Reverse(bis));
            {
                reveal ToNatRight();
            }
            2 * ToNatRight(Reverse(bis)) + 1;
            2 * bit_rev_int(i, bound) + 1;
        }
    }

}