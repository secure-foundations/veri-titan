module CutomBitVector {
    datatype cbv_raw = cbv_raw(
        vals: seq<bool>,
        len: nat
    )

    type cbv = t: cbv_raw |
        |t.vals| == t.len witness cbv_raw([], 0)

    type cbv384 = t: cbv | 
        t.len == 384

    type cbv768 = t: cbv | 
        t.len == 768

    method concat(v1: cbv, v2: cbv) returns (v3: cbv)
    {
        return cbv_raw(v1.vals + v2.vals, v1.len + v2.len);
    }

    // method rshift(v1: bv, )

}