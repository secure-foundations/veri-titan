include "SystemFFI.dfy"
include "BitVector.dfy"
include "NativeTypes.dfy"

include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

import opened CutomBitVector
import opened NativeTypes

// method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
//   ensures a[..] == s
// {
//     a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
// }

method get_random_bv(l: uint32) returns (v: cbv)
    ensures |v| == l;
{
    var a := new uint1[l];
    var i := 0;

    while i < l
        decreases l - i;
        invariant i <= l;
    {
        var b := SystemFFI.GetRandomBit();
        a[i] := b as uint1;
        i := i + 1;
    }

    v := a[..];
}

method simple_test(x: cbv)
    requires |x| == 768;
{
    var r1: cbv := cbv_slice(x, 0, 385);
    cbv_print("r1", r1);
    var q1: cbv := cbv_lsr(x, 383);
    cbv_print("q1", q1);
}

method {:main} Main()
{
    // var x := get_random_bv(768);
    var x  := from_nat(0x778f467950ba8aecb6dd8f7b865757e7a510c901b9d50297727b7c284d640eb9135cadc39237aa29ae0813517b58a83731875308a2cd045f1a6a4fb59a4d026bcd8164c3de1b71062e90b431439988a2cef26b707ce224ba84e1b431bf90e3fa, 768);
    cbv_print("x", x);
    simple_test(x);
}
