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

    function method {:opaque} merge_even_odd_indexed_items<T>(a: seq<T>, b: seq<T>, len: pow2_t): (r: seq<T>)
        requires |a| == |b| == len.full;
        ensures |r| == pow2_double(len).full;
        ensures even_indexed_items(r, pow2_double(len)) == a;
        ensures odd_indexed_items(r, pow2_double(len)) == b;
    {
        pow2_basics(len);
        var new_len := pow2_double(len);
        var r := seq(new_len.full, n requires 0 <= n < new_len.full => 
            if n % 2 == 0 then a[n/2] else b[n/2]);
        assert even_indexed_items(r, new_len) == a by {
            reveal even_indexed_items();
        }
        assert odd_indexed_items(r, new_len) == b by {
            reveal odd_indexed_items();
        }
        r
    }
}