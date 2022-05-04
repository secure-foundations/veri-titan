include "bins.dfy"
include "pows_of_2.dfy"

module ntt_index {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened bins

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

    lemma bit_rev_int_lemma2(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(2 * i, pow2_double(bound)) == bit_rev_int(i, bound);
    {
        var dbound := pow2_double(bound);
        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(2 * i, dbound.exp);

        assert bdis[0] == 0 && bdis[1..] == bis by {
            BitSelModEquivalence(bdis, 0);
            LemmaPow0(2);
            LemmaModMultiplesBasic(2 * i, 2);
            assert bdis[0] == 0 % 2;
            LemmaSmallMod(0, 2);
            LemmaFundamentalDivModConverse(2 * i, 2, i, 0);

            assert ToNatRight(bdis) == 2 * ToNatRight(bdis[1..]) by {
                reveal ToNatRight();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[1..]);
            LemmaSeqEq(bdis[1..], bis);
        }

        calc == {
            bit_rev_int(2 * i, dbound);
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == Reverse(bdis[1..]) + [0];
            }
            ToNatRight(Reverse(bdis[1..]) + [0]);
            ToNatRight(Reverse(bis) + [0]);
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis) + [0]);
            }
            ToNatLeft(Reverse(bis) + [0]);
            {
                reveal ToNatLeft();
            }
            ToNatLeft(Reverse(bis)) + 0 * Pow(2, bound.exp);
            {
                LemmaMulByZeroIsZeroAuto();
            }
            ToNatLeft(Reverse(bis));
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis));

            }
            bit_rev_int(i, bound);
        }
    }

    lemma bit_rev_int_lemma3(i: nat, bound: pow2_t)
        requires i < bound.full;
        ensures bit_rev_int(2 * i + 1, pow2_double(bound)) ==  bit_rev_int(i, bound) + bound.full;
    {
        var dbound := pow2_double(bound);
        var j := 2 * i + 1;

        reveal Pow2();

        var bis := FromNatWithLen(i, bound.exp);
        var bdis := FromNatWithLen(j, dbound.exp);

        assert bdis[0] == 1 && bdis[1..] == bis by {
            BitSelModEquivalence(bdis, 0);
            LemmaPow0(2);
            LemmaModMultiplesBasic(2 * i, 2);
            assert bdis[0] == 1 % 2;
            LemmaSmallMod(1, 2);
            LemmaFundamentalDivModConverse(j, 2, i, 1);

            assert ToNatRight(bdis) == 2 * ToNatRight(bdis[1..]) + 1 by {
                reveal ToNatRight();
            }

            LemmaToNatLeftEqToNatRight(bdis);
            LemmaToNatLeftEqToNatRight(bdis[1..]);
            LemmaSeqEq(bdis[1..], bis);
        }

        calc == {
            bit_rev_int(j, pow2_double(bound));
            ToNatRight(Reverse(bdis));
            {
                assert Reverse(bdis) == Reverse(bdis[1..]) + [1];
            }
            ToNatRight(Reverse(bdis[1..]) + [1]);
            ToNatRight(Reverse(bis) + [1]);
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis) + [1]);
            }
            ToNatLeft(Reverse(bis) + [1]);
            {
                reveal ToNatLeft();
            }
            ToNatLeft(Reverse(bis)) + 1 * Pow(2, bound.exp);
            ToNatLeft(Reverse(bis)) + bound.full;
            {
                LemmaToNatLeftEqToNatRight(Reverse(bis));
            }
            bit_rev_int(i, bound) + bound.full;
        }
    }
}