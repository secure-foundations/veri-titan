include "ntt_index.i.dfy"
include "poly_view.i.dfy"

module ntt_twiddle_i(MQ: ntt_param_s) {
        import opened Power
        import opened Power2
        import opened DivMod
        import opened Mul

        import opened pow2_s
        import opened ntt_index

        import MQP = mq_poly_i(MQ)
        import PV = poly_view_i(MQ)

        type elem = MQ.elem
        type elems = MQ.elems

        const Q := MQ.Q;
        const R := MQ.R;
        const PSI := MQ.PSI;
        const OMEGA := MQ.OMEGA;
        const OMEGA_INV := MQ.OMEGA_INV;

        const N := MQ.N; 

        lemma primitive_root_non_zero_lemma(i: nat)
                requires i < N.full * 2;
                ensures MQP.mqpow(PSI, i) != 0;
        {
                var PSI := PSI;
                if Pow(PSI, i) % Q == 0 {
                        var j := N.full * 2 - i;
                        calc == {
                                1;
                                {
                                        MQ.Nth_root_lemma();
                                }
                                Pow(PSI, i + j) % Q;
                                {
                                        LemmaPowAdds(PSI, i, j);
                                }
                                (Pow(PSI, i) * Pow(PSI, j)) % Q;
                                {
                                        LemmaMulModNoopGeneral(Pow(PSI, i), Pow(PSI, j), Q);
                                }
                                (Pow(PSI, i) % Q * (Pow(PSI, j) % Q)) % Q;
                                (0 * (Pow(PSI, j) % Q)) % Q;
                                (0) % Q;
                                0;
                        }
                        assert false;
                }
        }

        lemma full_rotation_lemma(a: nat)
                ensures MQP.mqpow(PSI, a + 2 * N.full) == MQP.mqpow(PSI, a);
        {
                var PSI := PSI;
                var N := N.full;
                calc == {
                        Pow(PSI, a + 2 * N) % Q;
                        {
                                LemmaPowAdds(PSI, a, 2 * N);
                        }
                        (Pow(PSI, a) * Pow(PSI, 2 * N)) % Q;
                        {
                                LemmaMulModNoopGeneral(Pow(PSI, a), Pow(PSI, 2 * N), Q);
                        }
                        ((Pow(PSI, a) % Q) * (Pow(PSI, 2 * N) % Q)) % Q;
                        {
                                MQ.Nth_root_lemma();
                                assert Pow(PSI, 2 * N) % Q == 1;
                        }
                        (Pow(PSI, a) % Q) % Q;
                        {
                                LemmaModBasicsAuto();
                        }
                        Pow(PSI, a) % Q;
                }
        }

        lemma inv_full_rotation_lemma(a: nat)
                ensures MQP.mqpow(OMEGA_INV, a + N.full) == MQP.mqpow(OMEGA_INV, a);
        {
                var N := N.full;
                MQ.Nth_root_lemma();

                calc == {
                        1;
                        {
                                Lemma1Pow(N);
                        }
                        Pow(1, N) % Q;
                        Pow(1 % Q, N) % Q;
                        Pow((OMEGA * OMEGA_INV) % Q, N) % Q;
                        {
                                LemmaPowModNoop(OMEGA * OMEGA_INV, N, Q);
                        }
                        Pow(OMEGA * OMEGA_INV, N) % Q;
                        {
                                LemmaPowDistributes(OMEGA, OMEGA_INV, N);
                        }
                        (Pow(OMEGA, N) * Pow(OMEGA_INV, N)) % Q;
                        {
                                LemmaMulModNoopGeneral(Pow(OMEGA, N), Pow(OMEGA_INV, N), Q);
                        }
                        ((Pow(OMEGA, N) % Q) * (Pow(OMEGA_INV, N) % Q)) % Q;
                        ((Pow(OMEGA_INV, N)) % Q) % Q;
                        {
                                LemmaModBasicsAuto();
                        }
                        Pow(OMEGA_INV, N) % Q;
                }

                calc == {
                        Pow(OMEGA_INV, a + N) % Q;
                        {
                                LemmaPowAdds(OMEGA_INV, a, N);
                        }
                        (Pow(OMEGA_INV, a) * Pow(OMEGA_INV, N)) % Q;
                        {
                                LemmaMulModNoopGeneral(Pow(OMEGA_INV, a), Pow(OMEGA_INV, N), Q);
                        }
                        ((Pow(OMEGA_INV, a) % Q) * (Pow(OMEGA_INV, N) % Q)) % Q;
                        {
                                assert Pow(OMEGA_INV, N) % Q == 1;
                        }
                        (Pow(OMEGA_INV, a) % Q) % Q;
                        {
                                LemmaModBasicsAuto();
                        }
                        Pow(OMEGA_INV, a) % Q;
                }
        }

        lemma half_rotation_lemma(a: nat)
                ensures Pow(PSI, a + N.full) % Q == (Q - Pow(PSI, a) % Q) % Q;
        {
                var PSI := PSI;
                var N := N.full;
                var t0 := Pow(PSI, a);
                calc == {
                        Pow(PSI, a + N) % Q;
                        {
                                LemmaPowAdds(PSI, a, N);
                        }
                        (t0 * Pow(PSI, N)) % Q;
                        {
                                LemmaMulModNoopGeneral(t0, Pow(PSI, N), Q);
                        }
                        ((t0 % Q) * (Pow(PSI, N) % Q)) % Q;
                        {
                                MQ.Nth_root_lemma();
                                assert Pow(PSI, N) % Q == Q - 1;
                        }
                        ((t0 % Q) * (Q - 1)) % Q;
                        {
                                LemmaMulModNoopGeneral(t0, Q - 1, Q);
                        }
                        (t0 * (Q - 1)) % Q;
                        {
                                LemmaMulIsDistributive(t0, Q, -1);
                        }
                        (t0 * Q - t0) % Q;
                        {
                                LemmaModMultiplesVanish(t0, -t0, Q);
                        }
                        (- t0) % Q;
                        {
                                LemmaModMultiplesVanish(1, -t0, Q);
                        }
                        (Q - t0) % Q;
                        {
                                LemmaSubModNoop(Q, t0, Q);
                        }
                        (Q - Pow(PSI, a) % Q) % Q;
                }
        }

        lemma inv_half_rotation_lemma(a: nat)
                ensures (N.full / 2) * 2 == N.full;
                ensures Pow(OMEGA_INV, a + N.full / 2) % Q == (Q - Pow(OMEGA_INV, a) % Q) % Q;
        {
                MQ.Nth_root_lemma();
                pow2_basics_lemma(N);
                var HN := N.full / 2;
                var t0 := Pow(OMEGA_INV, a);

                calc == {
                        Pow(OMEGA_INV, a + HN) % Q;
                        {
                                LemmaPowAdds(OMEGA_INV, a, HN);
                        }
                        (t0 * Pow(OMEGA_INV, HN)) % Q;
                        {
                                LemmaMulModNoopGeneral(t0, Pow(OMEGA_INV, HN), Q);
                        }
                        ((t0 % Q) * (Pow(OMEGA_INV, HN) % Q)) % Q;
                        {
                                MQ.Nth_root_lemma();
                                assert Pow(OMEGA_INV, HN) % Q == Q - 1;
                        }
                        ((t0 % Q) * (Q - 1)) % Q;
                        {
                                LemmaMulModNoopGeneral(t0, Q - 1, Q);
                        }
                        (t0 * (Q - 1)) % Q;
                        {
                                LemmaMulIsDistributiveAuto();
                        }
                        (t0 * Q - t0) % Q;
                        {
                                LemmaModMultiplesVanish(t0, -t0, Q);
                        }
                        (- t0) % Q;
                        {
                                LemmaModMultiplesVanish(1, -t0, Q);
                        }
                        (Q - t0) % Q;
                        {
                                LemmaSubModNoop(Q, t0, Q);
                        }
                        (Q - t0 % Q) % Q;
                }
        }

        lemma twiddle_factors_index_bound_lemma(t: pow2_t, j: nat)
                returns (d: pow2_t)
                requires t.exp < N.exp;
                requires j < t.full;
                ensures t.full + j < N.full;
                ensures d == pow2_half(PV.block_count(t));
                ensures 2 * j < PV.block_size(d).full;
        {
                assert t.full <= N.full / 2 by {
                        reveal Pow2();
                        LemmaPowIncreases(2, t.exp, N.exp-1);
                        assert pow2(N.exp-1) == pow2_half(pow2(N.exp));
                        assert pow2(N.exp-1).full == N.full / 2;
                }
                calc {
                        t.full + j;
                        <
                        2 * t.full;
                        <=
                        2 * (N.full / 2);
                        {
                                pow2_basics_lemma(N);
                        }
                        N.full;
                }

                d := PV.block_count(t);
                assert PV.block_size(d) == t;

                calc {
                        2 * j;
                        <
                        2 * t.full;
                        2 * PV.block_size(d).full;
                        pow2_double(PV.block_size(d)).full;
                        {
                                PV.block_count_half_lemma(d);
                        }
                        PV.block_size(pow2_half(d)).full;
                }

                d := pow2_half(PV.block_count(t));
        }
}
