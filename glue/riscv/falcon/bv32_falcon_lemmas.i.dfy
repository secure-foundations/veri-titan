include "../../generic_falcon_lemmas.dfy"
include "mq_arith_lemmas.dfy"

module bv32_falcon_lemmas refines generic_falcon_lemmas {
    import opened Seq
    import opened Power2
    import opened DivModNeg
    import opened rv_machine
    import opened rv_vale
    import opened mem
    import flat
    import opened bv32_op_s

    import opened mq_arith_lemmas
    import MWD = bv16_op_s

    predicate elems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_elems(iter.buff)
    }

    predicate nelems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(iter, heap, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_nelems(iter.buff)
    }

    // lemma bit_rev_index_lemma(
    //     a: seq<nat>,
    //     ftable: seq<nat>,
    //     sbi: uint32,
    //     rsbi: uint32,
    //     ti: nat,
    //     a0: uint32,
    //     t0: uint32,
    //     t1: uint32)

    //     requires |a| == N.full;
    //     requires bit_rev_ftable_wf(ftable);

    //     requires 0 <= 2 * ti + 1 < |ftable|;
    //     requires sbi == ftable[2 * ti];
    //     requires rsbi == ftable[2 * ti+1];
    
    //     requires flat.ptr_admissible_32(heap_b32_index_ptr(a0, N.full / 2 - 1));

    //     requires t0 == uint32_add(a0, uint32_ls(sbi, 1));
    //     requires t1 == uint32_add(a0, uint32_ls(rsbi, 1));

    //     ensures t0 == a0 + 2 * sbi;
    //     ensures t1 == a0 + 2 * rsbi;

    //     ensures sbi == build_view(a, ti, N).get_split_index();
    //     ensures rsbi == bit_rev_int(ftable[2 * ti], N);
    // {
    //     var table := ftable_cast(ftable);
    //     assert ti < |table|;

    //     assert table[ti].0 == ftable[2 * ti]
    //         && table[ti].1 == ftable[2 * ti + 1] by {
    //         reveal ftable_cast();
    //     }

    //     assert table[ti].0 == build_view(a, ti, N).get_split_index()
    //         && table[ti].1 == bit_rev_int(table[ti].0, N) by {
    //         reveal table_wf();
    //         reveal table_wf_inner();
    //     }

    //     // ftable_index_lemma(a, ftable, table, ti);
    //     assert sbi == build_view(a, ti, N).get_split_index();
    //     assert rsbi == bit_rev_int(ftable[2 * ti], N);

    //     ls1_lemma(sbi);
    //     ls1_lemma(rsbi);
    // }



    lemma denormalize_lemma(buff: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires valid_nelems(buff);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == uint32_srai(a1, 31);
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures valid_nelem(buff[i]);
        ensures d == MQN.denormalize(as_nelem(buff[i]));
    {
        assert valid_nelem(buff[i]);

        var a0 :uint16 := buff[i];
        var sa0 := as_nelem(a0);
        assert sa0 < 0 ==> a1 == a0 as nat + 0xffff0000;
        assert sa0 >= 0 ==> a1 == a0;

        if to_int32(a1) >= 0 {
            assert sa0 >= 0;
            assert b == 0 by { lemma_rs_by_31(to_int32(a1)); }
            lemma_uint32_and_Q(b);
            assert c == 0;
            assert d == a0;
            assert d == MQN.denormalize(as_nelem(a0));
        }
        else {
            assert sa0 < 0;
            assert int32_rs(to_int32(a1), 31) == -1 by { lemma_rs_by_31(to_int32(a1)); }
            lemma_uint32_and_Q(b);
            assert c == Q;
            assert d == sa0 + Q;
            assert d == MQN.denormalize(as_nelem(a0));
        }
    }

    lemma denormalization_peri_lemma(buff: seq<uint16>, dnv: seq<uint16>, i: nat, a1: uint32, b: uint32, c: uint32, d: uint32)
        requires valid_nelems(buff);
        requires valid_elems(dnv);
        requires denorm_inv(buff, dnv, i);
        requires i < |buff|;
        requires a1 == uint16_sign_ext(buff[i]);
        requires b == uint32_srai(a1, 31);
        requires c == uint32_and(b, Q);
        requires d == uint32_add(a1, c);
        ensures valid_nelem(buff[i]);
        ensures d == MQN.denormalize(as_nelem(buff[i]));
        ensures valid_elems(dnv[i := lh(d)]);
        ensures denorm_inv(buff, dnv[i := lh(d)], i + 1);
    {
        reveal valid_elems();
        var lh, uh := lh(d), uh(d);
        half_split_lemma(d);
        denormalize_lemma(buff, i, a1, b, c, d);
        assert d == lh;
    }


    lemma normalization_pre_lemma(inputs: seq<uint16>)
        requires valid_elems(inputs);
        ensures norm_inv(inputs, inputs, 0);
    {
        reveal norm_inv();
    }

    function cond_Q(src: uint32): uint32
    {
        if to_int32(src) >= 0 then 0 else 12289
    }

    lemma normalization_peri_lemma(outputs: seq<uint16>, inputs: seq<uint16>, i: nat, value: uint32, diff: uint32, mask: uint32, rst: uint32)
        requires norm_inv(outputs, inputs, i);
        requires i < |outputs|;
        requires value == uint16_sign_ext(outputs[i])
        requires diff == uint32_sub(Q/2, value);
        requires mask == cond_Q(diff);
        requires rst == uint32_sub(value, mask);
        ensures norm_inv(outputs[i := lh(rst)], inputs, i + 1);
    {
        reveal valid_elems();
        reveal norm_inv();

        assert value == outputs[i];
        half_split_lemma(rst);
        var lh, uh := lh(rst), uh(rst);

        if to_int32(diff) >= 0 {
            assert as_nelem(rst) == MQN.normalize(value);
        } else {
            if to_int32(rst) < 0 {
                assert uh == 0xffff; // the upper bits all set
            } else {
                assert uh == 0; // the upper bits all clear
            }
        }
        assert as_nelem(lh) == MQN.normalize(value);
    }

    lemma normalization_post_lemma(outputs: seq<uint16>, inputs: seq<uint16>)
        requires valid_elems(inputs);
        requires norm_inv(outputs, inputs, 512);
        ensures valid_nelems(outputs);
    {
        reveal norm_inv();
    }

    const NORMSQ_BOUND := integers.BASE_31

    lemma accumulate_lemma(v16: uint16, sum: uint32, sum': uint32,
        over: uint32, over': uint32, gsum: nat)
        returns (gsum': nat)
        requires msb(over) == 1 ==> gsum >= NORMSQ_BOUND;
        requires msb(over) == 0 ==> sum == gsum < NORMSQ_BOUND;

        requires valid_nelem(v16);
        requires var v32 := uint16_sign_ext(v16);
            sum' == uint32_add(sum, uint32_mul(v32, v32));
        requires over' == uint32_or(over, sum');

        ensures gsum' == gsum + as_nelem(v16) * as_nelem(v16);
        ensures msb(over') == 1 ==> gsum' >= NORMSQ_BOUND;
        ensures msb(over') == 0 ==> sum' == gsum' < NORMSQ_BOUND;
    {
        var v32 := uint16_sign_ext(v16);
        var iv16 :int := bv16_op_s.to_int16(v16);
        var iv32 :int := to_int32(v32);
        var p := uint32_mul(v32, v32);
        gsum' := gsum + p;

        mul_equiv_lemma(iv32, iv32);

        assert -12289 <= iv16 <= 12289;
        assume 0 <= iv16 * iv16 <= 151019521;

        calc == {
            p;
            (iv32 * iv32) % 0x100000000;
            (iv16 * iv16) % 0x100000000;
            {
                LemmaSmallMod(151019521, 0x100000000);
            }
            (iv16 * iv16);
        }

        assert msb(sum') == 1 ==> msb(over') == 1 by {
            reveal or();
        }
        assert msb(over) == 1 ==> msb(over') == 1 by {
            reveal or();
        }
        assume (msb(sum') == 0 && msb(over) == 0)
            ==> msb(over') == 0;
    }

    lemma is_short_post_lemma(s1: seq<uint16>, s2: seq<uint16>, 
        sum: uint32, sum': uint32, over: uint32, over': uint32, gsum: nat)
        requires valid_nelems(s1);
        requires valid_nelems(s2);
        requires gsum == l2norm_squared(s1, s2, N.full);
        requires msb(over) == 1 ==> gsum >= NORMSQ_BOUND;
        requires msb(over) == 0 ==> sum == gsum < NORMSQ_BOUND;
        requires over' == uint32_srai(over, 31);
        requires sum' == or(over', sum);
        ensures gsum < NORMSQ_BOUND ==> sum' == sum;
        ensures gsum >= NORMSQ_BOUND ==> sum' == 0xffff_ffff;
    {
        lemma_rs_by_31(to_int32(over));

        if (msb(over) == 0) {
            assert over' == 0;
            assert sum' == sum by {
                reveal or();
            }
        } else {
            assert over' == 0xffff_ffff;
            assert sum' == 0xffff_ffff by {
                reveal or();
            }
        }
    }
}
