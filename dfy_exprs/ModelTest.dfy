include "SystemFFI.dfy"
include "BitVector.dfy"
include "NativeTypes.dfy"

include "../otbn_model/lib/powers.dfy"
include "../otbn_model/lib/congruences.dfy"

import opened CutomBitVector
import opened NativeTypes

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

// t = [w25, w24]
// q2' = [w18, w17]
// q1 = [w8, w9]
method simple_test(a: cbv, b: cbv)
    requires |a| == 512;
    requires |b| == 512;
{
//   bn.rshi w20, w18, w31 >> 128
//   bn.rshi w19, w17, w18 >> 128
    var t1 := cbv_lsr(a, 128);
    cbv_print("t1", t1);

//   bn.add w19, w19, w8
//   bn.addc w20, w20, w9
    var t2 := cbv_add(t1, b);
    cbv_print("t2", t2);
}

method {:main} Main()
{
    // var x := get_random_bv(768);
    var a := from_nat(0xf7ce980efe5b7c893b50a6dc801e033186d6169d9c82733527427cb872aea951091cd3f7207d94ffe99e1eed7acd4a30e59cd2ccf6bdde731cce04314b8e6148, 512);

    var b := from_nat(0x4b4dc1dd7c9923cd49b5248c63b43c6f638b623f931693147ce65c14f4e87afa0a4600b6d088d4538f41a54ed81d496edd2a9b0a7c779b3af1f924313e20ada7, 512);

    simple_test(a, b);
}
