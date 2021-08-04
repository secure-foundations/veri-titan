include "../spec/rsa_ops.dfy"
include "../dafny_library/NonlinearArithmetic/Power.dfy"
include "../dafny_library/NonlinearArithmetic/DivMod.dfy"
include "../dafny_library/Sequences/Seq.dfy"

module addc512_lemmas {
    import opened bv_ops
    import opened vt_ops
    import opened rsa_ops
    import opened vt_consts
    import opened Power
    import opened DivMod
    import NT = NativeTypes
    import S = Seq
    import refining_NatSeq

    lemma addc_256_op_lemma(
        x: uint256, y: uint256, z: uint256, c: uint1)
        requires (z, c) == uint256_addc(x, y, 0);
        ensures seq_addc([x], [y]) == ([z], c);
    {
        var (a, b) := refining_NatSeq.seq_add([x], [y]);
        assert [] + [z] == [z];
        calc {
            seq_addc([x], [y]);
            refining_NatSeq.seq_add([x], [y]);
            (a, b);
        }

    }

    lemma addc_512_op_lemma(
        x0: uint256, y0: uint256, z0: uint256, c0: uint1,
        x1: uint256, y1: uint256, z1: uint256, c1: uint1)
        requires (z0, c0) == uint256_addc(x0, y0, 0);
        requires (z1, c1) == uint256_addc(x1, y1, c0);
        ensures seq_addc([x0, x1], [y0, y1]) == ([z0, z1], c1);
    {
        addc_256_op_lemma(x0, y0, z0, c0);
        assert [z0] + [z1] == [z0, z1];

        reveal refining_NatSeq.seq_add();
        var (a, b) := refining_NatSeq.seq_add([x0, x1], [y0, y1]);
        calc {
            seq_addc([x0, x1], [y0, y1]);
            refining_NatSeq.seq_add([x0, x1], [y0, y1]);
            (a, b);
        }
    }

    predicate seq_addc_512_is_safe(xs: seq<uint256>, ys: seq<uint256>)
        requires |xs| == |ys| == 2;
    {
        to_nat(xs) + to_nat(ys) < pow_B256(2)
    }

    lemma mont_word_mul_add_bound_lemma_0(
        xs: seq<uint256>, ys: seq<uint256>, a: uint256, b: uint256)
        requires |xs| == |ys| == 2;
        requires to_nat(xs) == a * b;
        requires S.last(ys) == 0;
        ensures seq_addc_512_is_safe(xs, ys);
    {
        var c := S.first(ys);
        calc {
            to_nat(xs) + to_nat(ys);
            == { to_nat_lemma_1(ys); }
            a * b + c;
            < { single_digit_lemma_1(a, b, c, NT.BASE_256 - 1); }
            NT.BASE_256 * NT.BASE_256;
            == { reveal power(); }
            pow_B256(2);
        }
    }

    lemma mont_word_mul_add_bound_lemma_1(
        xs: seq<uint256>, ys: seq<uint256>, a: uint256, b: uint256, c: uint256)
        requires |xs| == |ys| == 2;
        requires to_nat(xs) == a * b + c;
        requires S.last(ys) == 0;
        ensures seq_addc_512_is_safe(xs, ys);
    {
        var d := S.first(ys);
        calc {
            to_nat(xs) + to_nat(ys);
            == { to_nat_lemma_1(ys); }
            a * b + c + d;
            < { single_digit_lemma_2(a, b, c, d, NT.BASE_256 - 1); }
            NT.BASE_256 * NT.BASE_256;
            == { reveal power(); }
            pow_B256(2);
        }
    }

    lemma seq_addc_512_safe_nat_lemma(
        xs: seq<uint256>, ys: seq<uint256>, zs: seq<uint256>, cout: uint1)
        requires |xs| == 2 && |ys| == 2;
        requires seq_addc(xs, ys) == (zs, cout);
        requires seq_addc_512_is_safe(xs, ys);
        ensures to_nat(xs) + to_nat(ys) == to_nat(zs);
        ensures to_nat(zs) < NT.BASE_512
    {
        assert pow_B256(2) == NT.BASE_512 by {
            reveal power();
        }
        seq_addc_nat_lemma(xs, ys, zs, cout);
        if cout == 1 {
            assert false; // prove by contradiction
        }
        assert to_nat(xs) + to_nat(ys) == to_nat(zs);
    }
}