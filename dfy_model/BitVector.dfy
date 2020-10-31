include "NativeTypes.dfy"
include "../otbn_model/lib/powers.dfy"

module CutomBitVector {
    import opened NativeTypes
    import opened powers

    datatype cbv_raw = cbv_raw(
        vals: seq<uint2>,
        len: uint32
    )

    type cbv = t: cbv_raw |
        |t.vals| == t.len && t.len >= 1
        witness cbv_raw([0], 1)

    type cbv384 = t: cbv | 
        t.len == 384

    type cbv768 = t: cbv | 
        t.len == 768

    method concat(v1: cbv, v2: cbv) returns (v3: cbv)
        requires 0 < v1.len + v2.len <= UINT32_MAX;
        ensures v3.vals == v1.vals + v2.vals;
    {
        return cbv_raw(v1.vals + v2.vals, v1.len + v2.len);
    }

    method lsb(v: cbv) returns (b: uint2)
    {
        b := v.vals[0];
    }

    method msb(v: cbv) returns (b: uint2)
    {
        b := v.vals[|v.vals| - 1];
    }

    method slice(v: cbv, lo: uint32, hi: uint32) returns (v': cbv)
        requires 0 <= lo < hi <= v.len;
        ensures v'.vals == v.vals[lo..hi];
    {
        v' := cbv_raw(v.vals[lo..hi], hi - lo);
    }

    function method to_nat(v: cbv) : nat 
    {
        to_nat_aux(v.vals)
    }

    function method to_nat_aux(vals: seq<uint2>) : nat
    {
        if |vals| == 0 then 0
        else vals[0] + 2 * to_nat_aux(vals[1..])
    }

    method cbv_test()
    {
        var a: cbv := cbv_raw([1, 1, 1, 0, 1], 5);
        assert to_nat(a) == 23;

        var a': cbv := slice(a, 1, 5);
        assert a'.vals == [1, 1, 0, 1];
        assert to_nat(a') == 11;
    }
}