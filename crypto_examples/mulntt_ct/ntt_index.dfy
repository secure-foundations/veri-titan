include "nth_root.dfy"
include "../ntt_cleanup/pow2.dfy"

module ntt_index {
    import opened Seq

    import opened nth_root
    import opened pows_of_2

    function method {:opaque} even_indexed_items<T>(a: seq<T>, len: pow2_t): seq<T>
        requires |a| == len.full;
    {
        pow2_basics(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2])
    }

    function method {:opaque} odd_indexed_items<T>(a: seq<T>, len: pow2_t): seq<T>
        requires |a| == len.full;
    {
        pow2_basics(len);
        seq(len.full/2, n requires 0 <= n < len.full/2 => a[n * 2 + 1])
    }

    predicate {:opaque} unifromly_sized(blocks: seq<seq<elem>>, bsize: pow2_t)
    {
        && (forall i: nat | i < |blocks| :: |blocks[i]| == bsize.full)
    }
}