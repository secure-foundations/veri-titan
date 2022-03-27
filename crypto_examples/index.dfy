include "omega.dfy"
include "bins.dfy"

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
        && 1 <= idx.bound.exp == |idx.bins| // exp is the number of bits, we have at least 1 bit
        && idx.v < idx.bound.full
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

    function method lsb(idx: index_t): (lsb: uint1)
        ensures lsb == First(idx.bins);
    {
        valid_index_correspondence(idx);
        idx.v % 2
    }

    function method bit_rev_index(idx: index_t): (new_idx: index_raw)
        requires idx.bound.exp < N == Pow(2, L);
        ensures valid_index(new_idx);
        ensures new_idx.bins == Reverse(idx.bins);
        // ensures forall i: 0 <= i < |idx.bin| ==>
        //     new_idx.bin[i] == idx.bin[idx.bound.full - i - 1];
        decreases idx.bound.exp;
    {
        if idx.bound.exp == 1 then idx
        else pow2_basics(idx.bound);
            var lsb, v' := idx.v % 2, idx.v / 2;
            var bound' := pow2_half(idx.bound);
            var bins' := DropFirst(idx.bins);
            valid_index_correspondence(idx);
            var temp := index_cons(v', bins', bound');
            var idx' := bit_rev_index(temp);
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
            assert idx'.bins + [lsb] == Reverse(idx.bins) by {
                reveal Reverse();
            }
            index_cons(idx'.v + lsb * bound'.full, idx'.bins + [lsb], idx.bound)
    }

    predicate ntt_indicies_wf(idxs: seq<index_t>, len: pow2_t)
    {
        && len.exp <= L
        && |idxs| == len.full
        && (forall i: nat :: i < len.full ==> 
            idxs[i].bound == pow2(L))
    }

    predicate ntt_indicies_inv(idxs: seq<index_t>, len: pow2_t)
    {
        && ntt_indicies_wf(idxs, len)
        && (forall i: nat :: i < len.full ==> 
            ToNatRight(idxs[i].bins[(L - len.exp)..]) == i)
    }

    lemma ntt_indicies_inv_base_case(idxs: seq<index_t>, len: pow2_t)
        requires len == pow2(L)
        requires ntt_indicies_wf(idxs, len)
        requires forall i: nat :: i < len.full ==> idxs[i].v == i;
        requires ntt_indicies_inv(idxs, len)
    {
        forall i: nat | i < len.full
            ensures ToNatRight(idxs[i].bins[0..]) == i
        {
            calc == {
                ToNatRight(idxs[i].bins[0..]);
                ToNatRight(idxs[i].bins);
                idxs[i].v;
                i;
            }
        }
    }

    function method even_indexed_indices(idxs: seq<index_t>, len: pow2_t): (idx': seq<index_t>)
        requires |idxs| == len.full >= 2;
        ensures |idx'| == len.full / 2;
    {
        pow2_basics(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => idxs[n * 2])
    }

    lemma even_indexed_indices_reorder(idxs: seq<index_t>, len: pow2_t, idxs': seq<index_t>)
        requires len.full >= 2;
        requires ntt_indicies_inv(idxs, len); 
        requires even_indexed_indices(idxs, len) == idxs';
        ensures ntt_indicies_inv(idxs', pow2_half(len));
    {
        var len' := pow2_half(len);
        assert ntt_indicies_wf(idxs', len');

        forall i: nat | i < len'.full
            ensures ToNatRight(idxs'[i].bins[(L - len'.exp)..]) == i
        {
            var bins := idxs[i * 2].bins;
            assert bins == idxs'[i].bins;

            var offset := L - len.exp;
            var prev := bins[offset..];
            var curr := bins[offset+1..];

            calc == {
                2 * i;
                ToNatRight(prev);
                {
                    assert [bins[offset]] + curr == prev;
                    assert DropFirst(prev) == curr;
                    reveal ToNatRight();
                }
                ToNatRight(curr) * 2 + bins[offset];
                {
                    LemmaSeqLswModEquivalence(prev);
                    assert ToNatRight(prev) == 2 * i;
                    assert bins[offset] == 0;
                }
                ToNatRight(curr) * 2;
            }

            calc == {
                i;
                ToNatRight(curr);
                ToNatRight(idxs'[i].bins[(L - len'.exp)..]);
            }
        }
    }
}