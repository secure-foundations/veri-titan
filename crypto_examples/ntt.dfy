include "pow2.dfy"
include "omega.dfy"
include "ntt_rec.dfy"

module ntt {
    import opened Seq
    import opened Power
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas
    import opened ntt_rec

    function A(): seq<elem>
        ensures |A()| == N == pow2(L).full;

    function Ar(): seq<elem>
        ensures |Ar()| == N == pow2(L).full;
        // ensures forall i | 0 <= i < N :: Ar()[i] == 

    lemma index_bounded_lemma(
        j: nat, k: nat, ki: nat,
        m: pow2_t, step_count: pow2_t)
        requires m.full >= 2;
        requires 0 <= j < m.full / 2;
        requires N == pow2(L).full;
        requires 1 <= m.exp <= L;
        requires step_count == pow2_div(pow2(L), m);
        requires k == ki * m.full;
        requires ki < step_count.full;
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
        <= { assert ki + 1 <= step_count.full; LemmaMulInequalityAuto(); }
            step_count.full * m.full;
        ==
            N;
        }
    }

    // lemma ntt_chunk_base_case(a': seq<elem>, 
    //     k: nat, ki: nat, t: elem, u: elem,
    //     m: pow2_t, step_count: pow2_t)

    //     requires |a'| == N == pow2(L).full;
    //     requires m.exp == 1;
    //     // requires step_count == pow2_div(pow2(L), m);
    //     // requires k == ki * m.full;
    //     // requires ki < step_count.full;
    //     requires k < k + 1 < N;
    
    //     requires t == modmul(1, Ar()[k + 1]);
    //     requires u == Ar()[k];
    //     requires a'[k] == modadd(u, t);
    //     requires a'[k+1] == modsub(u, t);
    //     // ensures 
    // {
    //     calc == {
    //         t;
    //         modmul(1, Ar()[k + 1]);
    //         (Ar()[k + 1]) % Q;
    //         {
    //             assume false;
    //         }
    //         Ar()[k + 1];
    //     }

    //     var len := pow2(0);
    //     pow2_basics(len);

    //     var even := Ar()[k..k+1];
    //     var odd := Ar()[k+1..k+2];

    //     ntt_rec_base_case(odd, len);
    //     ntt_rec_base_case(even, len);

    //     assert t == poly_eval(odd, omega_nk(len, 0));
    //     assert u == poly_eval(even, omega_nk(len, 0));

    //     var omg := omega_nk(len, 0);

    //     y_k_value(even + odd, even, odd, pow2(0), pow2(1),
    //             omg, k,
    //             y_e_k: elem, y_o_k: elem, y_k: elem)
    // }

    method ntt_chunk_loop(a: seq<elem>,
        k: nat, ki: nat,
        m: pow2_t, step_count: pow2_t)
    returns (a': seq<elem>)
        // combine two chunks into one
        requires |a| == N == pow2(L).full;
        requires 1 <= m.exp <= L;
        requires step_count == pow2_div(pow2(L), m);
        requires k == ki * m.full;
        requires ki < step_count.full;
        requires m.exp == 1 ==> a == Ar();
    {
        a' := a;
        var half_step := m.full / 2;
        var omgm := omega_n(m);

        var omg := 1;
        var j := 0;

        assert omg == modpow(omgm, 0) by {
            LemmaPow0Auto();
        }

        pow2_basics(m);

        index_bounded_lemma(0, k, ki, m, step_count);

        while (j < half_step)
            invariant 0 <= j <= half_step;
            invariant omg == modpow(omgm, j);
            invariant |a'| == |a|;
            invariant k + j + half_step <= N;
            invariant a[..k] == a'[..k];
            invariant a[k+j..k+half_step] == a'[k+j..k+half_step];
            invariant a[k+half_step+j..] == a'[k+half_step+j..];

        {
            index_bounded_lemma(j, k, ki, m, step_count);
            var t := modmul(omg, a[k + j + half_step]);
            var u := a[k + j];
            a' := a'[k + j := modadd(u, t)];
            a' := a'[k + j + half_step := modsub(u, t)];

            omg_inv(omgm, omg, m, j);
            omg := modmul(omg, omgm);

            // if half_step == 1 {
            //     ntt_chunk_base_case(a', k, ki, t, u, m, step_count);
            // }

            j := j + 1;
        }

        assert a[..k] == a'[..k];
        assert a[k+m.full..] == a'[k+m.full..];

        if m.exp == 1 {
            assert half_step == 1;
            // j := 0;
            // index_bounded_lemma(j, s, k, ki, m, step_count);

            // var t := modmul(omg, a[k + j + half_step]);
            // var u := a[k + j];

            // assert half_step == 1;
            // assert a'[k + j] == modadd(u, t);

        }
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
    //     var step_size := m.full;

    //     var step_count := pow2_div(pow2(L), m);
    //     // assert step_count.exp == L - m.exp;
    
    //     var k := 0;
    //     var ki := 0;

    //     while (ki < step_count.full) // at level s, each chunck is 2 ** s big
    //         // invariant step_count == pow2_div(pow2(L), m);
    //         // invariant step_count.exp == L - m.exp;
    //         invariant 0 <= k == ki * step_size;
    //     {
    //         var k' := k + step_size;
    //         var ki' := ki + 1;

    //         var _ := ntt_chunk_loop(a, k, ki, m, step_count);

    //         assert k' == (ki + 1) * step_size by {
    //             LemmaMulIsDistributiveAddOtherWay(step_size, ki, 1);
    //             assert (ki + 1) * step_size == ki * step_size + 1 * step_size;
    //         }
    //         assert (ki + 1) * step_size > 0 by {
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

