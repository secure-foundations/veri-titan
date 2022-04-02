include "../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

module bins refines LittleEndianNat {
    function method BASE(): nat
    {
        2
    }

    lemma BitSelModEquivalence(a: seq<uint>, i: nat)
        requires 0 <= i < |a|;
        ensures Pow(2, i) > 0;
        ensures IsModEquivalent(a[i], ToNatRight(a) / Pow(2, i), 2);
        ensures a[i] == (ToNatRight(a) / Pow(2, i)) % 2;
    {
        LemmaSeqPrefix(a, i);
        assert ToNatRight(a[..i]) + ToNatRight(a[i..]) * Pow(2, i) == ToNatRight(a);
        LemmaSeqNatBound(a[..i]);
        // LemmaPowStrictlyIncreasesAuto();
        assert ToNatRight(a[..i]) < Pow(2, i);
        LemmaFundamentalDivModConverse(ToNatRight(a), Pow(2, i), ToNatRight(a[i..]), ToNatRight(a[..i]));

        assert ToNatRight(a) / Pow(2, i) == ToNatRight(a[i..]);
        LemmaSeqLswModEquivalence(a[i..]);
    }

    lemma SubSeqReverseProperty<T>(s: seq<T>, i: nat)
        requires 0 < i <= |s|;
        ensures Reverse(s[i..]) + [s[i-1]] == Reverse(s[i-1..]);
    {
        var l1 := |s| - i;
        var l2 := |s| - i + 1;
        var s1, s2 := s[i..], s[i-1..];

        var x := Reverse(s1);
        var y := Reverse(s2);

        assert forall j | 0 <= j < l1 :: x[j] == s1[l1 - j - 1];
        assert forall j | 0 <= j < l2 :: y[j] == s2[l2 - j - 1];

        forall j | 0 <= j < l1
            ensures x[j] == y[j];
        {
        }

        assert x + [y[l1]] == y;
        assert y[l1] == s2[0] == s[i - 1];

        assert x + [s[i-1]] ==  y;
    }

    lemma ReverseSymmetric<T>(s: seq<T>)
        ensures Reverse(Reverse(s)) == s;
    {
    }

    lemma SubsequenceIndex<T>(s: seq<T>, a: nat, b: nat, c: nat)
        requires a <= b <= |s|;
        requires c < b - a;
        ensures s[a..b][c] == s[a + c];
    {
        var s' := s[a..b];
        assert s'[c] == s[a + c];
    }
}