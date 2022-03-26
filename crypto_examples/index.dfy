include "omega.dfy"
include "../std_lib/src/Collections/Sequences/LittleEndianNat.dfy"

module bins refines LittleEndianNat {
    function method BASE(): nat
    {
        2
    }
}

module rindex {
    import opened Power
    import opened Seq

    import opened omegas
    import opened pows_of_2
    import opened bins

    type uint1   =  i: nat | i < 2

    datatype index_raw = index_cons(v: nat, bins: seq<uint1>, bound: pow2_t)

    predicate valid_index(idx: index_raw)
    {
        && idx.v < idx.bound.full
        && |idx.bins| == idx.bound.exp // exp is the number of bits
        && idx.v == ToNatRight(idx.bins)
    }

    type index_t =  i: index_raw | valid_index(i) witness *

    function method build_index(v: nat): index_t
        requires v < N;
    {
        nth_root_lemma();
        index_cons(v, FromNatWithLen(v, L), pow2(L))
    }

    lemma valid_index_correspondence(idx: index_t)
        requires 1 <= idx.bound.exp 
        ensures idx.v % 2 == First(idx.bins);
        ensures idx.v / 2 == ToNatRight(DropFirst(idx.bins));
    {
        pow2_basics(idx.bound);
        var lsb, v' := idx.v % 2, idx.v / 2;
        var bins' := DropFirst(idx.bins);
        reveal ToNatRight();
        assert lsb == First(idx.bins);
        assert v' == ToNatRight(bins');
    }

    function method reverse_bits(idx: index_t): (new_idx: index_raw)
        requires 1 <= idx.bound.exp < N == Pow(2, L);
        ensures valid_index(new_idx);
        decreases idx.bound.exp
    {
        if idx.bound.exp == 1 then idx
        else pow2_basics(idx.bound);
            var lsb, v' := idx.v % 2, idx.v / 2;
            var bound' := pow2_half(idx.bound);
            var bins' := DropFirst(idx.bins);
            valid_index_correspondence(idx);
            var temp := index_cons(v', bins', bound');
            var idx' := reverse_bits(temp);
            valid_index_correspondence(idx');
            assert idx'.v + lsb * bound'.full == ToNatRight(idx'.bins + [lsb]) by {
                calc == {
                    ToNatRight(idx'.bins + [lsb]);
                    {
                        LemmaToNatLeftEqToNatRight(idx'.bins + [lsb]);
                    }
                    ToNatLeft(idx'.bins + [lsb]);
                    {
                        reveal ToNatLeft();
                    }
                    ToNatLeft(idx'.bins) + lsb * Pow(2, idx.bound.exp - 1);
                    ToNatLeft(idx'.bins) + lsb * bound'.full;
                    {
                        LemmaToNatLeftEqToNatRight(idx'.bins);
                    }
                    idx'.v + lsb * bound'.full;
                }
            }
            assert idx'.v + lsb * bound'.full < idx.bound.full by {
                LemmaSeqNatBound(idx'.bins + [lsb]);
            }
            index_cons(idx'.v + lsb * bound'.full, idx'.bins + [lsb], idx.bound)
    }
}