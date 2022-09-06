include "falcon.s.dfy"
include "mq_ntt.i.dfy"
include "mq_poly.i.dfy"

module falcon_512_i refines
    falcon_s(ntt512_param_i, mq_poly_i(ntt512_param_i))
{
    import opened Mul
    import opened Power
    import opened DivMod

    import opened ntt_index
    import opened pow2_s

    import CMQ = ntt512_param_i
    import CMQP = mq_poly_i(CMQ)
    import CPV = poly_view_i(CMQ)

    import FNTT = mq_fntt_i(CMQ, CMQP, CPV)
    import INTT = mq_intt_i(CMQ, CMQP, CPV)

    type elem = MQ.elem
    type n_elems = MQ.n_elems
    type nelem = MQN.nelem

    const Q := MQ.Q;

    const R := MQ.R;
    const R_INV := MQ.R_INV;

    const PSI := MQ.PSI;
    const PSI_INV := MQ.PSI_INV;

    const OMEGA := MQ.OMEGA;
    const OMEGA_INV := MQ.OMEGA_INV;

    const N := MQ.N;
    const N_INV := MQ.N_INV;

    function bound(): nat {
        0x29845d6
    }

    predicate fntt_eval_all_alt(a: n_elems, poly: n_elems)
    {
        && var p_hat := MQP.scaled_coeff(poly);
        && (forall i | 0 <= i < N.full ::
            MQP.poly_eval(p_hat, MQP.mqpow(MQ.OMEGA, bit_rev_int(i, N))) == a[i])
    }

    lemma fntt_equi_lemma(a: n_elems, poly: n_elems)
        requires FNTT.ntt_eval_all(a, poly);
        ensures fntt_eval_all_alt(a, poly)
    {
        var p_hat: seq<elem> := MQP.scaled_coeff(poly);

        forall i | 0 <= i < N.full
            ensures MQP.poly_eval(p_hat, MQP.mqpow(PSI, 2 * bit_rev_int(i, N))) == a[i];
        {
            var index := 2 * bit_rev_int(i, N);
            var x := MQP.mqpow(PSI, index);
            var x_hat := MQP.mqpow(PSI, index + 1);

            var left := MQP.poly_terms(poly, x_hat);
            var right := MQP.poly_terms(p_hat, x);

            assert MQP.poly_eval(poly, x_hat) == a[i] by {
                reveal CPV.points_eval_suffix_inv();
                assert index * 1 == index;
            }

            assert left == right by {
                forall j | 0 <= j < N.full 
                    ensures left[j] == right[j];
                {
                    var x_j := MQP.mqpow(x, j);

                    LemmaMulStrictlyPositive(index, j);

                    assert x_j == MQP.mqpow(PSI, index * j) by {
                        MQP.mqpow_muls(PSI, index, j);
                    }
                    var poly_j := poly[j];

                    calc == {
                        left[j];
                        MQP.mqmul(poly_j, MQP.mqpow(x_hat, j));
                        MQP.mqmul(poly_j, MQP.mqpow(MQP.mqpow(PSI, index + 1), j));
                        {
                            MQP.mqpow_muls(PSI, index + 1, j);
                        }
                        MQP.mqmul(poly_j, MQP.mqpow(PSI, (index + 1) * j));
                        {
                            LemmaMulIsDistributiveAddOtherWayAuto();
                        }
                        MQP.mqmul(poly_j, MQP.mqpow(PSI, index * j + j));
                        {
                            MQP.mqpow_adds(PSI, index * j, j);
                        }
                        MQP.mqmul(poly_j, MQP.mqmul(x_j, MQP.mqpow(PSI, j)));
                        {
                            MQP.mqmul_commutes(x_j, MQP.mqpow(PSI, j));
                        }
                        MQP.mqmul(poly_j, MQP.mqmul(MQP.mqpow(PSI, j), x_j));
                        {
                            MQP.mqmul_associates(poly_j, MQP.mqpow(PSI, j), x_j);
                        }
                        MQP.mqmul(MQP.mqmul(poly_j, MQP.mqpow(PSI, j)), x_j);
                        MQP.mqmul(p_hat[j], MQP.mqpow(x, j));
                        right[j];
                    }
                }
            }

            assert MQP.poly_eval(p_hat, x) == a[i] by {
                reveal MQP.poly_eval();
                calc == {
                    MQP.poly_eval(poly, x_hat);
                    MQP.mqsum(left);
                    MQP.mqsum(right);
                    MQP.poly_eval(p_hat, x);
                }
            }
        }

        forall i | 0 <= i < N.full
            ensures MQP.poly_eval(p_hat, MQP.mqpow(MQ.OMEGA, bit_rev_int(i, N))) == a[i];
        {
            var index := bit_rev_int(i, N);
            calc == {
                MQP.mqpow(PSI, 2 * index);
                Pow(PSI, 2 * index) % Q;
                {
                    LemmaPowMultiplies(PSI, 2, index);
                }
                Pow(Pow(PSI, 2), index) % Q;
                {
                    LemmaPowModNoop(Pow(PSI, 2), index, Q);
                }
                Pow(Pow(PSI, 2) % Q, index) % Q;
                {
                    MQ.Nth_root_lemma();
                }
                Pow(MQ.OMEGA % Q, index) % Q;
                {
                    LemmaPowModNoop(MQ.OMEGA, index, Q);
                }
                Pow(MQ.OMEGA, index) % Q;
                MQP.mqpow(MQ.OMEGA, index);
            }
        }
    }

    predicate is_mm_circle_product(c: n_elems, a: n_elems, b: n_elems, i: nat)
        requires i <= N.full
    {
        forall j: nat | 0 <= j < i ::
            c[j] == MQP.montmul(a[j], b[j])
    }

    lemma poly_mod_product_lemma(
        a0: n_elems, a1: n_elems, b0: n_elems, b1: n_elems,
        p0: n_elems, p1: n_elems, p2: n_elems, p3: n_elems, p4: n_elems)

        requires FNTT.ntt_eval_all(a1, a0);
        requires FNTT.ntt_eval_all(b1, b0);
        requires p0 == CMQP.circle_product(a1, b1);
        requires is_bit_rev_shuffle(p0, p1, N);
        
        requires INTT.ntt_eval_all(p2, p1);
        requires is_bit_rev_shuffle(p2, p3, N);
        requires is_mm_circle_product(
            p4, p3, MQP.inverse_ntt_scaling_table(), N.full);
        ensures p4 == poly_mod_product(a0, b0);
    {
        fntt_equi_lemma(a1, a0);
        fntt_equi_lemma(b1, b0);

        var a_hat := MQP.scaled_coeff(a0);
        var b_hat := MQP.scaled_coeff(b0);

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA, bit_rev_int(i, N));
                MQP.mqmul(MQP.poly_eval(a_hat, x), MQP.poly_eval(b_hat, x)) == p0[i];
        {
        }

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA, i);
                MQP.mqmul(MQP.poly_eval(a_hat, x), MQP.poly_eval(b_hat, x)) == p1[i];
        {
            reveal is_bit_rev_shuffle();
            bit_rev_symmetric(i, N);
            assert p1[i] == p0[bit_rev_int(i, N)];
        }

        assert p1 == MQP.circle_product(MQP.NTT(MQP.scaled_coeff(a0)), 
            MQP.NTT(MQP.scaled_coeff(b0)));

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA_INV, bit_rev_int(i, N));
                MQP.poly_eval(p1, x) == p2[i];
        {
            reveal CPV.points_eval_suffix_inv();
            assert bit_rev_int(i, N) * 1 == bit_rev_int(i, N);
        }

        forall i | 0 <= i < N.full
            ensures var x := MQP.mqpow(MQ.OMEGA_INV, i);
                MQP.poly_eval(p1, x) == p3[i];
        {
            reveal is_bit_rev_shuffle();
            bit_rev_symmetric(i, N);
            assert p3[i] == p2[bit_rev_int(i, N)];
        }
        var inverse := MQP.INTT(p1);

        forall i | 0 <= i < N.full
            ensures inverse[i] == (p3[i] * N_INV) % Q
        {}

        forall i | 0 <= i < N.full
            ensures p4[i] == (inverse[i] * MQP.mqpow(PSI_INV, i)) % Q;
        {
            MQP.inverse_ntt_scaling_table_axiom(i);
            var t := MQP.mqpow(PSI_INV, i);
            var t0 := (t * N_INV) % Q;
            var t1 := (t0 * R) % Q;
            var t2 := inverse[i];
            assert p4[i] == (p3[i] * t1 * R_INV) % Q;

            gbassert IsModEquivalent(p4[i], t2 * t, Q) by {
                assert IsModEquivalent(R * R_INV, 1, Q) by {
                    MQ.Nth_root_lemma();
                }
                assert IsModEquivalent(t0, t * N_INV, Q);
                assert IsModEquivalent(t1, t0 * R, Q);
                assert IsModEquivalent(t2, p3[i] * N_INV, Q);
                assert IsModEquivalent(p4[i], p3[i] * t1 * R_INV, Q);
            }
        }

        assert p4 == MQP.negatively_wrapped_convolution(a0, b0);
        MQP.negatively_wrapped_convolution_lemma(a0, b0, p4);

    }
}