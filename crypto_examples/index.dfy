include "omega.dfy"
include "../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

module bin refines LittleEndianNat {
    function method BASE(): nat
    {
        2
    }
}

module rindex {
    import opened Power

    import opened omegas
    import opened pows_of_2
    import opened bin

    type uint1   =  i: nat | i < 2

    datatype index_raw = index_cons(v: nat, bin: seq<uint1>)

    predicate valid_index(idx: index_raw)
    {
        && idx.v < N == Pow(2, L)
        && idx.bin == FromNatWithLen(idx.v, L)
    }

    type index_t =  i: index_raw | valid_index(i) witness *

    function method build_index(v: nat): index_t
        requires v < N
    {
        nth_root_lemma();
        index_cons(v, FromNatWithLen(v, L))
    }
}