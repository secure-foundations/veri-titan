include "NativeTypes.dfy"

module CutomBitVector {
    import opened NativeTypes

    datatype cbv_raw = cbv_raw(
        vals: seq<uint2>,
        len: nat
    )

    type cbv = t: cbv_raw |
        |t.vals| == t.len && t.len >= 1
        witness cbv_raw([0], 1)

    type cbv384 = t: cbv | 
        t.len == 384

    type cbv768 = t: cbv | 
        t.len == 768

    method concat(v1: cbv, v2: cbv) returns (v3: cbv)
    {
        return cbv_raw(v1.vals + v2.vals, v1.len + v2.len);
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

    method test() 
    {
        var a: cbv := cbv_raw([1, 0, 1, 0, 1], 5);
        assert to_nat(a) == 21;
    }
}