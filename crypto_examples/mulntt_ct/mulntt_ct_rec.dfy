include "nth_root.dfy"
include "ntt_index.dfy"
include "polys.dfy"

module mulntt_ct_rec {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2

    import opened nth_root
    import opened ntt_index
    // function method A(): seq<elem>
    //     ensures |A()| == N == pow2(LOGN).full;

    function method block_count(m: pow2_t): nat
        requires 0 <= m.exp <= LOGN;
    {
        pow2_div(pow2(LOGN), m).full
    }

    lemma block_count_half_lemma(m: pow2_t)
        requires 1 <= m.exp <= LOGN;
        ensures block_count(pow2_half(m)) == block_count(m) * 2;
    {
        Nth_root_lemma();
        var left := pow2_div(pow2(LOGN), pow2_half(m));
        assert left.full * (m.full / 2) == N;
        var right := pow2_div(pow2(LOGN), m);
        var half := m.full / 2;
        pow2_basics(m);

        calc == {
            left.full * half;
            left.full * (m.full / 2);
            right.full * (2 * half);
            {
                LemmaMulIsAssociativeAuto();
            }
            (right.full * 2) * half;
        }
        LemmaMulEqualityConverse(half, left.full, right.full * 2);
    }

    datatype lpolys = lpolys_cons(blocks: seq<seq<elem>>, bsize: pow2_t)
    {
        predicate level_wf()
        {
            && unifromly_sized(blocks, bsize)
            && 0 <= bsize.exp <= LOGN
            && block_count(bsize) == |blocks|
        }

        function method {:opaque} build_smaller_level(): (lps: lpolys)
            requires level_wf();
            requires 1 <= bsize.exp <= LOGN;
            ensures lps.level_wf();
            ensures lps.bsize == pow2_half(bsize);
            ensures |lps.blocks| == 2 * |blocks|;
        {
            reveal unifromly_sized();
            pow2_basics(bsize);
            block_count_half_lemma(bsize);
            var new_size := pow2_half(bsize);
            var new_count := |blocks| * 2;
            var new_blocks := seq(new_count, n requires 0 <= n < new_count => 
                if n % 2 == 0 then even_indexed_items(blocks[n/2], bsize)
                else odd_indexed_items(blocks[n/2], bsize));
            lpolys_cons(new_blocks, new_size)
        }

        // lemma base_level_correct()
        //     requires blocks == [A()];
        //     requires bsize.exp == LOGN;
        //     ensures level_wf();
        // {
        //     reveal level_wf();
        //     Nth_root_lemma();
        //     assert bsize.full == N;
        // }

        lemma level_index_correspondence_lemma(i: nat, sl: lpolys)
            requires level_wf();
            requires 1 <= bsize.exp <= LOGN;
            requires sl == build_smaller_level();
            requires i < |blocks|;
            ensures |blocks[i]| == bsize.full;
            ensures 2 * i + 1 < |sl.blocks|;
            ensures even_indexed_items(blocks[i], bsize) == sl.blocks[2 * i];
            ensures |sl.blocks[2 * i]| == pow2_half(bsize).full;
            ensures odd_indexed_items(blocks[i], bsize) == sl.blocks[2 * i + 1];
            ensures |sl.blocks[2 * i + 1]| == pow2_half(bsize).full;
        {
            reveal unifromly_sized();
            reveal build_smaller_level();
        }
    }

    // function method build_lpolys(bsize: pow2_t): (lps: lpolys)
    //     requires bsize.exp <= LOGN;
    //     ensures lps.level_wf();
    //     ensures lps.bsize == bsize;
    //     decreases LOGN - bsize.exp;
    // {
    //     if bsize.exp == LOGN then
    //         var l := lpolys_cons([A()], bsize);
    //         l.base_level_correct();
    //         l
    //     else
    //         var prev := build_lpolys(pow2_double(bsize));
    //         // assert 1 <= pow2_double(bsize).exp <= LOGN;
    //         prev.build_smaller_level()
    // }

    // function method build_all_lpolys(): seq<lpolys>
    // {

    // }
}