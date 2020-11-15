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

// t = [w25, w24]
// q2' = [w18, w17]
// q1 = [w8, w9]
method simple_test(t: cbv, q1: cbv, q2': cbv)
    requires |q2'| == 768;
{
//   /* q2'' = q2' >> 384 = [w20, w19] = [w18, w17, w16] >> 384
//                                     = [w18, w17] >> 128 */
//   bn.rshi w20, w18, w31 >> 128
//   bn.rshi w19, w17, w18 >> 128
    var q2'' := cbv_lsr(q2', 128);
//   /* Add q1. This is unconditional since MSb of u is always 1.
//      This cannot overflow due to leading zeros.
//      q2''' = q2'' + q1 = [w20, w19] = [w20, w19] + [w8, w9] */

//   bn.add w19, w19, w8
//   bn.addc w20, w20, w9
    var q2''' := cbv_add(q2'', q1);

//   /* Conditionally add u (without leading 1) in case of MSb of x being set.
//      This is the "real" q2 but shifted by 384 bits to the right. This cannot
//      overflow due to leading zeros
//      q2'''' = x[767]?q2'''+u[383:0]:q2'''
//             = [w20, w19] + [w25, w24] = q2 >> 384 */
//   bn.add w19, w19, w24
//   bn.addc w20, w20, w25
    var q2'''' := cbv_add(q2''', t);

//   /* finally this gives q3 by shifting the remain bit to the right
//      q3 = q2 >> 385 = q2'''' >> 1 = [w9, w8] = [w20, w19] >> 1 */
//   bn.rshi w9, w20, w31 >> 1
//   bn.rshi w8, w19, w20 >> 1
    var q3 := cbv_lsr(q2'''', 1);
}

method {:main} Main()
{
    // var x := get_random_bv(768);
    var x  := from_nat(0x778f467950ba8aecb6dd8f7b865757e7a510c901b9d50297727b7c284d640eb9135cadc39237aa29ae0813517b58a83731875308a2cd045f1a6a4fb59a4d026bcd8164c3de1b71062e90b431439988a2cef26b707ce224ba84e1b431bf90e3fa, 768);
    // cbv_print("x", x);
    // simple_test(x);
}
