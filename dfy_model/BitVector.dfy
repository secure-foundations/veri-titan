include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"

module CutomBitVector {
    import opened NativeTypes
    import opened powers

    type cbv = t: seq<uint2> | |t| != 0

    type cbv384 = t: cbv | |t| == 384

    type cbv768 = t: cbv | |t| == 768

    // method zero(l: uint32) returns (v: cbv)
    //     ensures 
    // {

    // }

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

    function method to_nat(v: cbv) : nat
        decreases v;
    {
        if |v| == 0 then 0
        else v[0] + 2 * to_nat(v[1..])
    }

    method cbv_test()
    {
        var a: cbv := [1, 1, 1, 0, 1];
        assert to_nat(a) == 23;

        var a': cbv := slice(a, 1, 5);
        assert a' == [1, 1, 0, 1];
        assert to_nat(a') == 11;
    }
}