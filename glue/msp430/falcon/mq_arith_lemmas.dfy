include "../../../spec/arch/msp430/machine.s.dfy"
include "../../../spec/bvop/bv16_op.s.dfy"
include "../../../spec/arch/msp430/vale.i.dfy"
include "../../../spec/crypto/falcon512.i.dfy"
include "../../generic_falcon_lemmas.dfy"

module mq_arith_lemmas refines generic_falcon_lemmas {
    import opened Seq
    import opened Power2
    import opened bv16_op_s
    import opened bv16_seq
    import opened msp_machine
    import opened msp_vale

    import opened mem
    import flat

    import MWD = bv16_op_s

    type uint32_view_t = dw_view_t

    function BASE(): nat
    {
        BVSEQ.BASE()
    }

    lemma general_dw_add_lemma(
        xs: seq<uint>, ys: seq<uint>, zs: seq<uint>,
        c1: uint1, c2: uint1)
    returns (z: dw_view_t)
        requires |xs| == |ys| == |zs| == 2;
        requires (zs[0], c1) == addc(xs[0], ys[0], 0);
        requires (zs[1], c2) == addc(xs[1], ys[1], c1);
        ensures z.lh == zs[0];
        ensures z.uh == zs[1];
        ensures z.full == to_nat(zs);
        ensures z.full + c2 * BASE() * BASE() == to_nat(xs) + to_nat(ys);
    {
        var x_full := to_nat(xs);
        var y_full := to_nat(ys);
        var z_full := to_nat(zs);

        BVSEQ.LemmaSeqLen2(xs);
        BVSEQ.LemmaSeqLen2(ys);
        BVSEQ.LemmaSeqLen2(zs);

        var x_lh, x_uh := xs[0], xs[1];
        var y_lh, y_uh := ys[0], ys[1];
        var z_lh, z_uh := zs[0], zs[1];

        assert x_full == x_lh + x_uh * BASE();
        assert y_full == y_lh + y_uh * BASE();
        assert z_full == z_lh + z_uh * BASE();

        calc == {
            z_uh * BASE() + c2 * BASE() * BASE();
            {
                LemmaMulProperties();
            }
            (z_uh + c2 * BASE()) * BASE();
            {
                assert z_uh + c2 * BASE() == x_uh + y_uh + c1;
            }
            (x_uh + y_uh + c1) * BASE();
            {
                LemmaMulProperties();
            }
            x_uh * BASE() + y_uh * BASE() + c1 * BASE();
            {
                assert x_lh + y_lh == z_lh + c1 * BASE();
            }
            x_uh * BASE() + y_uh * BASE() + x_lh + y_lh - z_lh;
        }

        assert z_full + c2 * BASE() * BASE() == x_full + y_full;
        z := build_dw_view(z_lh, z_uh);
    }

    lemma cond_set_Q_lemma(flags0: flags_t, mask: uint16, flags1: flags_t)
        requires (mask, flags1) == msp_subc(0, 0, flags0);
        ensures uint16_and(12289, mask) == if flags0.cf == 0 then 12289 else 0;
    {
        assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
        assert uint16_and(Q, 0) == 0 by { reveal_and(); }
    }

    // lemma lemma_mq_add_correct(sum: uint16, mask: uint16, r: uint16, x: uint16, y: uint16)
    //     requires 0 <= x < 12289;
    //     requires 0 <= y < 12289;
    //     requires sum == msp_add(x, msp_add(y, 0xcfff).0).0;
    //     requires mask == msp_sub(0, if sum >= 0x8000 then 1 else 0).0;
    //     requires r == msp_add(sum, uint16_and(12289, mask)).0;
    //     ensures r == MQP.mqadd(x, y);
    // {
    //     assert Q == 12289;

    //     // d == x + y - Q
    //     assert IsModEquivalent(sum, x + y - Q, BASE_16);

    //     // -Q <= d < Q
    //     assert 0 <= x + y < 2*Q;
    //     assert (-(Q as int)) <= x + y - Q < Q;

    //     if sum >= 0x8000 {
    //         assert mask == 0xFFFF;
    //         assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
    //         assert IsModEquivalent(r, x + y, Q);
    //     } else {
    //         assert mask == 0;
    //         assert uint16_and(Q, 0) == 0 by { reveal_and(); }
    //         assert IsModEquivalent(r, x + y, Q);
    //     }
    // } 

    // lemma lemma_mq_sub_correct(diff: uint16, flags: flags_t, mask: uint16, r: uint16, x: int, y: int)
    //     requires 0 <= x < 12289;
    //     requires 0 <= y < 12289;
    //     requires var (d, f) := msp_sub(x, y);
    //              diff == d && flags == f;
    //     requires mask == msp_sub(0, if x - y >= 0 then 0 else 1).0;
    //     requires var (s, _) := msp_subc(0, 0xFFFF, flags);
    //              mask == s;
    //     requires r == msp_add(diff, uint16_and(12289, mask)).0;
    //     ensures r == MQP.mqsub(x, y);
    // {
    //     var Q : int := 12289;
        
    //     assert IsModEquivalent(diff, x - y, BASE_16);
        
    //     if get_cf(flags) == 0 {
    //         assert mask == 0xFFFF;
    //         assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
    //         assert IsModEquivalent(r, x - y, Q);
    //     } else {
    //         assert mask == 0;
    //         assert uint16_and(Q, 0) == 0 by { reveal_and(); }
    //         assert IsModEquivalent(r, x - y, Q);
    //     }
    // }

    // lemma lemma_cond_add_Q(flags: flags_t, mask: uint16, r: uint16, input: uint16)
    //     requires mask == msp_sub(0, if get_cf(flags) == 1 then 1 else 0).0;
    //     requires var (s, _) := msp_subc(0, 0, flags);
    //              mask == s;
    //     //requires input < BASE_16 - Q;
    //     requires r == msp_add(input, uint16_and(12289, mask)).0;
    //     ensures IsModEquivalent(r, input + if get_cf(flags) == 1 then Q else 0, BASE_16);
    // {
    //     if get_cf(flags) == 1 {
    //         assert mask == 0xFFFF;
    //         assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
    //     } else {
    //         assert mask == 0;
    //         assert uint16_and(Q, 0) == 0 by { reveal_and(); }
    //     }
    // }

    lemma montmul_lemma(x: uint16, y: uint16, cf: uint1, 
        xy_lh: uint16, xy_uh: uint16, sum: uint32_view_t, rr: uint16)
        requires x < Q;
        requires y < Q;
        requires to_nat([xy_lh, xy_uh]) == x * y;
        requires sum.full + cf * 0x100000000 == 
            x * y + mul(xy_lh, 12287) * 12289;
        requires rr == if sum.uh >= Q then sum.uh - Q else sum.uh;
        ensures rr == montmul(x, y);
    {
        var s_lh: nat, s_uh: nat := sum.lh, sum.uh;
        var s_full: nat := sum.full;
        var t := (xy_lh * 12287) % 65536;

        assert x * y + t * 12289 <= 956379136 by {
            LemmaMulUpperBound(x, Q, y, Q);
        }
        assert s_full == x * y + t * 12289 by {
            reveal dw_lh();
        }
        assert s_lh + s_uh * 65536 == s_full by {
            dw_view_lemma(sum);
        }
        assert x * y == xy_lh + xy_uh * 65536 by {
            bv16_seq.LemmaSeqLen2([xy_lh, xy_uh]);
        }

        gbassert IsModEquivalent(s_lh, 0, 65536) by {
            assert s_lh + s_uh * 65536 == x * y + t * 12289;
            assert x * y == xy_lh + xy_uh * 65536;
            assert IsModEquivalent(t, xy_lh * 12287, 65536);
        }

        LemmaSmallMod(s_lh, 65536);
        assert s_lh == 0;
        MQ.Nth_root_lemma();
        var R_INV := R_INV;
        var sub := if s_uh >= Q then 1 else 0;

        gbassert IsModEquivalent(rr, x * y * R_INV, 12289) by {
            assert rr == s_uh - sub * 12289;
            assert sub * (sub - 1) == 0;
            assert BASE_16 == 65536;
            assert s_uh * 65536 == x * y + t * 12289;
            assert x * y == xy_lh + xy_uh * 65536;
            assert IsModEquivalent(t, xy_lh * 12287, 65536);
            assert IsModEquivalent(1, R_INV * BASE_16, 12289);
        }

        assert s_uh * 65536 == s_full;
        assert s_uh <= 14593;
        LemmaSmallMod(rr, 12289);
        assume false;
    }

    predicate elems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(heap, iter) 
        && (address >= 0 ==> iter.cur_ptr() == address)
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && valid_elems(iter.buff)
    }

    predicate nelems_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(heap, iter)
        && (address >= 0 ==> iter.cur_ptr() == address)
        && (index >= 0 ==> iter.index == index)
        && valid_nelems(iter.buff)
    }

    // lemma norm_peri_lemma(outputs: seq<uint16>, inputs: seq<uint16>, i: nat,
    //     w: uint16, fg: flags_t, diff: uint16, mask: uint16, rst: uint16)
    //     requires norm_inv(outputs, inputs, i);
    //     requires i < |outputs|;
    //     requires w == outputs[i];
    //     requires (diff, fg) == msp_sub(6144, w);
    //     requires fg.cf == 1 ==> mask == 12289;
    //     requires fg.cf == 0 ==> mask == 0;
    //     requires rst == uint16_sub(w, mask);
    //     ensures norm_inv(outputs[i := rst], inputs, i + 1);
    // {
    //     reveal norm_inv();
    //     reveal valid_elems();

    //     if 6144 - w < 0 {
    //         assert mask == 12289;
    //     } else {
    //         assert mask == 0;
    //     }
    // }

    const NORMSQ_BOUND := 0x100000000

    lemma accumulate_lemma(v16: uint16,
        sum: uint32_view_t, sum': uint32_view_t,
        cf: uint1, mask: uint16,
        over: uint16, over': uint16, gsum: nat)
        returns (gsum': nat)

        requires over == 0xFFFF || over == 0;
        requires over == 0 ==> sum.full == gsum;
        requires over == 0xFFFF ==> gsum >= 0x100000000;

        requires valid_nelem(v16);
        requires sum'.full + 0x100000000 * cf 
            == sum.full + v16 * v16;

        requires mask == if cf == 1 then 0xFFFF else 0;
        requires over' == uint16_or(mask, over);

        ensures over' == 0xFFFF || over' == 0;
        ensures over' == 0 ==> sum'.full == gsum';
        ensures over' == 0xFFFF ==> gsum' >= 0x100000000;
        ensures gsum' == gsum + as_nelem(v16) * as_nelem(v16);
    {
        or_consts_lemma();
        var iv16 :int := bv16_op_s.to_int16(v16);
        assume 0 <= iv16 * iv16 <= 151019521;
        assume (iv16 * iv16) == v16 * v16;
        gsum' := gsum + v16 * v16;
    }

    lemma or_consts_lemma()
        ensures uint16_or(0xFFFF, 0xFFFF) == 0xFFFF;
        ensures uint16_or(0xFFFF, 0) == 0xFFFF;
        ensures uint16_or(0, 0xFFFF) == 0xFFFF;
        ensures uint16_or(0, 0) == 0;
    {
        reveal_or();
    }
}
