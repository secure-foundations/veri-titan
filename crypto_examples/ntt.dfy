include "ntt_rec.dfy"
include "index.dfy"

module ntt {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    import opened pows_of_2
    import opened omegas
    import opened ntt_rec
    import opened rindex

    function method A(): seq<elem>
        ensures |A()| == N == pow2(L).full;

    function method Ar(): seq<elem>
        ensures |Ar()| == N == pow2(L).full;
        ensures forall i | 0 <= i < N ::
            Ar()[i] == A()[build_rev_index(i).v];

    function method {:fuel 4} build_level_chunks(len: pow2_t): (cs: seq<seq<elem>>)
        requires 1 <= len.exp <= L
        ensures |cs| == pow2_div(pow2(L), len).full;
        ensures forall i | 0 <= i < |cs| :: |cs[i]| == len.full
        decreases L - len.exp
    {
        if len.exp == L then [A()]
        else 
            var a := build_level_chunks(pow2_double(len));
            assert |a| == pow2(L - len.exp - 1).full by {
                assert |a| == pow2(L).full / (pow2(len.exp + 1).full);
                reveal Pow2();
                assert len.exp + 1 <= L;
                LemmaPowSubtracts(2, len.exp + 1, L);
            }
            assert |a| * 2 == pow2(L - len.exp).full by {
                reveal Pow2();
                LemmaPowAdds(2, L - len.exp - 1, 1);
                LemmaPow1(2);
            }
            seq(|a| * 2, k requires 0 <= k < |a| * 2 => 
                if k % 2 == 0 then even_indexed_terms(a[k/2], len)
                else odd_indexed_terms(a[(k-1)/2], len))
    }

    function method get_level_chunk(len: pow2_t, ki: nat): (chunk: seq<elem>)
        requires 1 <= len.exp <= L
        requires ki < pow2_div(pow2(L), len).full;
        ensures |chunk| == len.full
    {
        build_level_chunks(len)[ki]
    }

    lemma index_bounded_lemma(
        j: nat, k: nat, ki: nat,
        m: pow2_t)
        requires m.full >= 2;
        requires 0 <= j < m.full / 2;
        requires N == pow2(L).full;
        requires 1 <= m.exp <= L;
        requires k == ki * m.full;
        requires ki < pow2_div(pow2(L), m).full;
        ensures k + j + m.full / 2 < N;
    {
        pow2_basics(m);
        var half_step := m.full / 2;

        calc {
            k + j + m.full / 2;
        ==
            ki * m.full + j + half_step;
        <
            ki * m.full + 2 * half_step;
        ==
            ki * m.full + m.full;
        == { LemmaMulIsDistributiveAddOtherWay(m.full, ki, 1); }
            (ki + 1) * m.full;
        <= { assert ki + 1 <= pow2_div(pow2(L), m).full; LemmaMulInequalityAuto(); }
            pow2_div(pow2(L), m).full * m.full;
        ==
            N;
        }
    }

    lemma ntt_chunk_base_case(a': seq<elem>, 
        k: nat, ki: nat, t: elem, u: elem,
        m: pow2_t)

        requires |a'| == N == pow2(L).full;
        requires m.exp == 1;
        requires ki < pow2_div(pow2(L), m).full;
        requires k == ki * m.full;
        requires k < k + 1 < N;

        requires t == modmul(1, Ar()[k + 1]);
        requires u == Ar()[k];
        requires a'[k] == modadd(u, t);
        requires a'[k+1] == modsub(u, t);

        ensures a'[k] == poly_eval(Ar()[k..k+2], omega_nk(m, 0));
        ensures a'[k+1] == poly_eval(Ar()[k..k+2], omega_nk(m, 1));
        // ensures Ar()[k..k+2] == get_level_chunk();
    {
        // nth_root_lemma();
        pow2_basics(m);
        var m' := pow2_half(m);

        assert t == Ar()[k + 1] by {
            assert Ar()[k + 1] < Q;
        }

        var even := Ar()[k..k+1];
        var odd := Ar()[k+1..k+2];
        var chunk :=Ar()[k..k+2];
        assert chunk == even + odd;

        var original := orignal_index(ki, 0, m);
        assert original.v == k;

        ntt_rec_base_case(odd, m');
        ntt_rec_base_case(even, m');

        assert u == poly_eval(even, omega_nk(m', 0));
        assert t == poly_eval(odd, omega_nk(m', 0));

        var omg := omega_nk(m, 0);

        calc == {
            modmul(omg, t);
            {
                LemmaPow0(omega_n(m));
            }
            modmul(1, t);
        }

        y_k_value(chunk, even, odd, pow2(0), pow2(1),
            omg, 0, u, t, a'[k]);

        y_k'_value(chunk, even, odd, pow2(0), pow2(1),
            omg, 0, u, t, a'[k+1]);
    }

    method ntt_chunk_loop(a: seq<elem>, k: nat, ki: nat, m: pow2_t)
    returns (a': seq<elem>)
        // this loop works on a chunk of size m.full
        // by combining two smaller chunks of size m.full/2
        // m.full: the chunk size at the current level
        requires |a| == N == pow2(L).full;
        // m.exp: the level, go from 1 to L (log N)
        requires 1 <= m.exp <= L;
        // ki: the chunk id at current level, go from 0 to N/m
        requires ki < pow2_div(pow2(L), m).full;
        // k is ki times chunk size, points to start of the chunk
        requires k == ki * m.full;

        requires m.exp == 1 ==> a == Ar();
    {
        a' := a;
        var len' := pow2_half(m);
        var omgm := omega_n(m);

        var omg := 1;
        var j := 0;

        assert omg == modpow(omgm, 0) by {
            LemmaPow0Auto();
        }

        pow2_basics(m);

        index_bounded_lemma(0, k, ki, m);

        while (j < len'.full)
            invariant 0 <= j <= len'.full;
            invariant omg == modpow(omgm, j);
            invariant |a'| == |a|;
            invariant k + j + len'.full <= N;
            invariant a[..k] == a'[..k];
            invariant a[k+j..k+len'.full] == a'[k+j..k+len'.full];
            invariant a[k+len'.full+j..] == a'[k+len'.full+j..];
        {
            index_bounded_lemma(j, k, ki, m);
            var t := modmul(omg, a[k + j + len'.full]);
            var u := a[k + j];
            a' := a'[k + j := modadd(u, t)];
            a' := a'[k + j + len'.full := modsub(u, t)];

           if m.exp == 1 {
                ntt_chunk_base_case(a', k, ki, t, u, m);
            }

            omg_inv(omgm, omg, m, j);
            omg := modmul(omg, omgm);
            j := j + 1;
        }

        assert a[..k] == a'[..k];
        assert a[k+m.full..] == a'[k+m.full..];
    }

    // method ntt_level_loop(a: seq<elem>, s: nat)
    //     requires |a| == N == pow2(L).full;
    //     requires 1 <= s < L;
    // {
    //     var m := pow2(s);
    //     pow2_basics(m);
    //     assume 1 <= m.full <= N/2;

    //     var omgm := omega_nk(m, 1);

    //     assert omega_nk(m, 1) == omega_n(m) by {
    //         LemmaPow1Auto();
    //     }

    //     var k := 0;
    //     var ki := 0;

    //     while (ki < pow2_div(pow2(L), m).full) 
    //         // at level s, each chunk is 2 ** s big
    //         // invariant step_count == pow2_div(pow2(L), m);
    //         // invariant step_count.exp == L - m.exp;
    //         invariant 0 <= k == ki * m.full;
    //     {
    //         var k' := k + m.full;
    //         var ki' := ki + 1;

    //         var _ := ntt_chunk_loop(a, k, ki, m);

    //         assert k' == (ki + 1) * m.full by {
    //             LemmaMulIsDistributiveAddOtherWay(m.full, ki, 1);
    //             assert (ki + 1) * m.full == ki * m.full + 1 * m.full;
    //         }
    //         assert (ki + 1) * m.full > 0 by {
    //             LemmaMulStrictlyPositiveAuto();
    //         }
    //         k, ki := k', ki';
    //     }
    // }

    // method ntt(b: seq<elem>, len: pow2_t) returns (y: seq<elem>)
    //     requires |b | == len.full == N;
    //     requires len.exp == L;
    //     // ensures poly_eval_all_points(a, y, len)
    // {
    //     // var s := pow2(0);
    //     var s := 1;
    //     while (s < L) // L levels totoal, combine results at each level 
    //         invariant 1 <= s;
    //     {
    //         ntt_level_loop(b, s);
    //         s := s + 1;
    //     }
    // }
}

