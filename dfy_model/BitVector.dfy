include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"

module CutomBitVector {
    import opened NativeTypes
    import opened powers

    type cbv = t: seq<uint2> | 0 < |t| <= UINT32_MAX witness [1]

    type cbv384 = t: cbv | |t| == 384

    type cbv768 = t: cbv | |t| == 768

    method zero(l: uint32) returns (v: cbv)
        ensures |v| == l;
        ensures to_nat(v) == 0; 
    {
        assume false;
    }

    method concat(v1: cbv, v2: cbv) returns (v3: cbv)
    {
        return v1 + v2; 
    }

    method lsb(v: cbv) returns (b: uint2)
    {
        b := v[0];
    }

    method msb(v: cbv) returns (b: uint2)
    {
        b := v[|v| - 1];
    }

    method slice(v: cbv, lo: uint32, hi: uint32) returns (v': cbv)
        requires 0 <= lo < hi <= |v|;
        ensures v' == v[lo..hi];
    {
        v' := v[lo..hi];
    }

    // function method to_nat(v: cbv) : nat
    //     decreases v;
    // {
    //     if |v| == 0 then 0
    //     else v[0] + 2 * to_nat(v[1..])
    // }

    function to_nat(v: cbv) : nat
    {
        to_nat_aux(v, |v|)
    }

    function {:fuel 10} to_nat_aux(v: cbv, i: uint32) : nat
        decreases i;
        requires 0 <= i <= |v|;
    {
        if i == 0 then 0
        else pow2(i - 1) * v[i - 1] + to_nat_aux(v, i - 1)
    }

    method cbv_test()
    {
        var a: cbv := [1, 1, 1, 0, 1];

        assert to_nat(a) == 23 by {
            reveal power();
        }

        // var a': cbv := slice(a, 1, 5);
        // assert a' == [1, 1, 0, 1];
        // assert to_nat(a') == 11;
    }
}