include "SystemFFI.dfy"
include "BitVector.dfy"
include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

import opened CutomBitVector

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
    a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method simple_test(x: cbv)
    requires |x| == 768;
{
    var r1: cbv := cbv_slice(x, 0, 385);
    var q1: cbv := cbv_lsr(x, 383);
}

method {:main} Main()
{
    var arr := SystemFFI.GetRandomBV(200);

    print "done!\n";
}
