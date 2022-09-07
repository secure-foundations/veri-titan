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

    type uint32_view_t = dw_view_t

    lemma lemma_mq_add_correct(sum: uint16, mask: uint16, r: uint16, x: uint16, y: uint16)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires sum == msp_add(x, msp_add(y, 0xcfff).0).0;
        requires mask == msp_sub(0, if sum >= 0x8000 then 1 else 0).0;
        requires r == msp_add(sum, uint16_and(12289, mask)).0;
        ensures r == MQP.mqadd(x, y);
    {
        assert Q == 12289;

        // d == x + y - Q
        assert IsModEquivalent(sum, x + y - Q, BASE_16);

        // -Q <= d < Q
        assert 0 <= x + y < 2*Q;
        assert (-(Q as int)) <= x + y - Q < Q;

        if sum >= 0x8000 {
            assert mask == 0xFFFF;
            assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
            assert IsModEquivalent(r, x + y, Q);
        } else {
            assert mask == 0;
            assert uint16_and(Q, 0) == 0 by { reveal_and(); }
            assert IsModEquivalent(r, x + y, Q);
        }
    } 

    lemma lemma_mq_sub_correct(diff: uint16, flags: flags_t, mask: uint16, r: uint16, x: int, y: int)
        requires 0 <= x < 12289;
        requires 0 <= y < 12289;
        requires var (d, f) := msp_sub(x, y);
                 diff == d && flags == f;
        requires mask == msp_sub(0, if x - y >= 0 then 0 else 1).0;
        requires var (s, _) := msp_subc(0, 0xFFFF, flags);
                 mask == s;
        requires r == msp_add(diff, uint16_and(12289, mask)).0;
        ensures r == MQP.mqsub(x, y);
    {
        var Q : int := 12289;
        
        assert IsModEquivalent(diff, x - y, BASE_16);
        
        if get_cf(flags) == 0 {
            assert mask == 0xFFFF;
            assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
            assert IsModEquivalent(r, x - y, Q);
        } else {
            assert mask == 0;
            assert uint16_and(Q, 0) == 0 by { reveal_and(); }
            assert IsModEquivalent(r, x - y, Q);
        }
    }

    lemma lemma_cond_add_Q(flags: flags_t, mask: uint16, r: uint16, input: uint16)
        requires mask == msp_sub(0, if get_cf(flags) == 1 then 1 else 0).0;
        requires var (s, _) := msp_subc(0, 0, flags);
                 mask == s;
        //requires input < BASE_16 - Q;
        requires r == msp_add(input, uint16_and(12289, mask)).0;
        ensures IsModEquivalent(r, input + if get_cf(flags) == 1 then Q else 0, BASE_16);
    {
        if get_cf(flags) == 1 {
            assert mask == 0xFFFF;
            assert uint16_and(Q, 0xFFFF) == Q by { reveal_and(); }
        } else {
            assert mask == 0;
            assert uint16_and(Q, 0) == 0 by { reveal_and(); }
        }
    }

    lemma lemma_montymul_correct(x: nat, y: nat, xy_lh: uint16, xy_uh: uint16, Q0Ixy:nat, sum: uint32_view_t, partial_lh: uint16, partial_uh: uint16, partial_uh_xy_uh:uint16, m: uint16, flags: flags_t, rr:uint16)
        requires x < Q;
        requires y < Q;
        requires to_nat([xy_lh, xy_uh]) == x * y;
        requires Q0Ixy == mul(xy_lh, 12287);
        requires sum.lh == partial_lh;
        requires sum.uh == partial_uh;
        requires sum.full == Q * Q0Ixy + xy_lh;
        requires partial_uh_xy_uh == msp_add(partial_uh, xy_uh).0;
        requires m == msp_sub(partial_uh_xy_uh, Q).0;
        requires flags == msp_sub(partial_uh_xy_uh, Q).1;
        requires IsModEquivalent(rr, m + if get_cf(flags) == 1 then Q else 0, BASE_16);
        ensures IsModEquivalent(rr * 4091, x * y, Q);
    {
        var v := (12287 * x * y) % BASE_16;
        assert x * y == xy_lh + xy_uh * BASE_16 by { bv16_seq.LemmaSeqLen2([xy_lh, xy_uh]); }
        assert xy_lh == (x * y) % BASE_16 by { LemmaModMultiplesVanish(xy_uh, xy_lh, BASE_16); }
        calc {
            Q0Ixy;
                { reveal dw_lh(); }
            (xy_lh * 12287) % BASE_16;
            (((x * y) % BASE_16) * 12287) % BASE_16;
                { LemmaMulModNoopGeneral(x*y, 12287, BASE_16); }
            ((x * y) * 12287) % BASE_16;
                { LemmaMulIsCommutativeAuto(); LemmaMulIsAssociativeAuto(); }
            v;
        }
        assert v == Q0Ixy;
        var w := Q * v;
        var xy := x * y;
        var z := partial_uh_xy_uh;

        // Establish a bound on xy_uh and partial_uh,
        // so we can show that their sum doesn't overflow

        // Bound xy_uh
        assert x * y <= (Q-1) * (Q-1) by { LemmaMulUpperBound(x, Q-1, y, Q-1); }
        assert x * y == BASE_16 * ((x * y)/BASE_16) + (x * y) % BASE_16 by { LemmaFundamentalDivMod(x*y, BASE_16); }
        assert x * y == BASE_16 * ((x * y)/BASE_16) + xy_lh;
        assert xy_uh * BASE_16 == BASE_16 * ((x * y)/BASE_16);
        assert xy_uh == (x * y) / BASE_16;
        assert (x * y) / BASE_16 <= ((Q-1) * (Q-1))/BASE_16 by { LemmaDivIsOrdered(x*y, (Q-1)*(Q-1), BASE_16); }
        assert xy_uh <= 2304;

        // Bound partial_uh
        calc {
            Q * Q0Ixy + xy_lh;
            sum.full;
            { dw_view_lemma(sum); }
            partial_lh + partial_uh * BASE_16; 
        }
        assert Q0Ixy < BASE_16;
        assert Q*Q0Ixy <= Q*(BASE_16-1) by { LemmaMulUpperBound(Q, Q, Q0Ixy, BASE_16-1); }
        assert Q*Q0Ixy + xy_lh <= Q*(BASE_16-1) + BASE_16; 
        assert (Q*Q0Ixy + xy_lh)/BASE_16 <= (Q*(BASE_16-1) + BASE_16) / BASE_16 by { LemmaDivIsOrdered(Q*Q0Ixy + xy_lh, Q*(BASE_16-1) + BASE_16, BASE_16); }
        assert (partial_lh + partial_uh * BASE_16)/BASE_16 <= (Q*(BASE_16-1) + BASE_16) / BASE_16;
        assert (partial_lh + partial_uh * BASE_16)/BASE_16 <= 12290;
        assert partial_uh <= 12290 by { LemmaDivMultiplesVanishFancy(partial_uh, partial_lh, BASE_16); }

        // Bringing the two bounds together:
        assert partial_uh + xy_uh < BASE_16;
        assert partial_uh_xy_uh == partial_uh + xy_uh;

        // Connect a 32-bit spec to our 16-bit calculations
        calc {
            Q * Q0Ixy + xy;
            Q * Q0Ixy + xy_lh + xy_uh * BASE_16;
            sum.full + xy_uh * BASE_16;
            calc {
                sum.full;
                    { dw_view_lemma(sum); }
                partial_lh + partial_uh * BASE_16; 
            }
            partial_lh + partial_uh * BASE_16 + xy_uh * BASE_16;
            { LemmaMulIsDistributiveAuto(); }
            partial_lh + (partial_uh + xy_uh) * BASE_16; 
            partial_uh_xy_uh * BASE_16 + partial_lh;
        }
        assert partial_uh_xy_uh * BASE_16 + partial_lh == Q * Q0Ixy + xy;

        gbassert IsModEquivalent(w + xy, 0, BASE_16) by {
            assert IsModEquivalent(v, 12287 * x * y, BASE_16);
            assert Q == 12289;
            assert BASE_16 == 65536;
            assert w == Q * v;
            assert xy == x * y;
        }

        DivMod.LemmaFundamentalDivMod(w + xy, BASE_16);
        assert w + xy == BASE_16 * (w+xy) / BASE_16 + (w+xy) % BASE_16;
        assert w + xy == BASE_16 * (w+xy) / BASE_16; 
        Power2.Lemma2To64();
        assert z * BASE_16 == w + xy;

        gbassert IsModEquivalent(rr * 4091, x * y, Q) by {
            assert IsModEquivalent(v, 12287 * x * y, BASE_16);
            assert Q == 12289;
            assert BASE_16 == 65536;
            assert IsModEquivalent(4091, BASE_16, Q);
            assert w == Q * v;
            assert xy == x * y;
            assert z * BASE_16 == (w + xy);
            assert IsModEquivalent(w + xy, 0, BASE_16);
            assert IsModEquivalent(rr, z, Q);
        }
    }

    predicate fvar_iter_inv(heap: heap_t, iter: b16_iter, address: int, index: int)
    {
        && b16_iter_inv(heap, iter) //, if address >= 0 then address else iter.cur_ptr())
        && (index >= 0 ==> iter.index == index)
        && |iter.buff| == N.full
        && contains_elems(iter.buff)
    }

    predicate is_nelem(e: uint16)
    {
        MQN.int_is_normalized(bv16_op_s.to_int16(e))
    }

    function as_nelem(e: uint16): nelem
        requires is_nelem(e)
    {
        bv16_op_s.to_int16(e)
    }

    predicate {:opaque} valid_nelems(a: seq<uint16>)
        ensures has_n_nelems(a) ==> |a| == N.full;
    {
        && |a| == N.full
        && (forall i | 0 <= i < |a| :: is_nelem(a[i]))
    }

    function as_nelems(a: seq<uint16>): (na: seq<nelem>)
        requires valid_nelems(a);
    {
        reveal valid_nelems();
        seq(|a|, i requires 0 <= i < |a| => as_nelem(a[i]))
    }
}