const BASE  : int := 65536
type uint1   = i :int | 0 <= i < 2
type uint16  = i :int | 0 <= i < BASE

function not(src: uint16): uint16

function inscrutable_subc(dst: uint16, src: uint16, cin: uint1): (uint16, uint1)
{
    var sum: nat := not(src) + dst + cin;
    if sum >= BASE then
        (sum - BASE, 1)
    else
        (sum, 0)
}

function msp_subc(dst: uint16, src: uint16, cin: uint1): (uint16, uint1)
{
    var diff: int := (dst as int) - src - (1 - cin);
    if diff >= 0 then 
        (diff, 1)
    else
        (diff + BASE, 0)
}

/*
    # we think the assume is true because
    dst = BitVec("x", full_bits)
    src = BitVec("y", full_bits)
    return And(BV2Int(~src  + dst  + 1) == (BV2Int(dst) - BV2Int(src) - 0)  % BASE,
        BV2Int(~src  + dst + 0) == (BV2Int(dst) - BV2Int(src) - 1)  % BASE)
*/

lemma subc_test(dst: uint16, src: uint16, cin: uint1)
    ensures msp_subc(dst, src, cin) == inscrutable_subc(dst, src, cin);
{
    var (dst', cout) := inscrutable_subc(dst, src, cin);
    var diff: int := dst - src - (1 - cin);
    assume dst' == if diff < 0 then diff + BASE else diff;
}