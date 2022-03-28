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
}