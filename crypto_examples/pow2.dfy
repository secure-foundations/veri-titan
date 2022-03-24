include "../std_lib/src/NonlinearArithmetic/Power2.dfy"
include "../std_lib/src/NonlinearArithmetic/DivMod.dfy"
include "../std_lib/src/Collections/Sequences/Seq.dfy"

module pows_of_2 {
    import opened Power
    import opened DivMod
    import opened Mul

    function method Pow2(e: nat): nat
    {
        LemmaPowPositive(2, e);
        Pow(2, e)
    }

    datatype pow2_t_raw = pow2_t_cons(full: nat, exp: nat)

    type pow2_t = n: pow2_t_raw | n.full == Pow2(n.exp) witness *

    function pow2(exp: nat): pow2_t
    {
        LemmaPowPositiveAuto();
        pow2_t_cons(Pow(2, exp), exp)
    }

    lemma pow2_basics(n: pow2_t)
        ensures n.exp == 0 ==> n.full == 1
        ensures n.exp == 1 ==> n.full == 2
        ensures n.exp != 0 ==> n.full % 2 == 0
    {
        reveal Pow();
    }

    // lemma pow2_double(n: pow2_t) returns (n': pow2_t)
    //     ensures n'.exp == n.exp + 1
    //     ensures n'.full == 2 * n.full
    // {
    //     var m := pow2_t_cons(2 * n.full, n.exp + 1);

    //     calc == {
    //         m.full;
    //         2 * n.full;
    //         2 * Pow2(n.exp);
    //         {
    //             reveal Pow();
    //         }
    //         Pow2(n.exp + 1);
    //         Pow2(m.exp);
    //     }

    //     n' := m;
    // }

    function method pow2_half(n: pow2_t) : (n': pow2_t)
        requires n.exp != 0 || n.full != 1;
        ensures n'.exp == n.exp - 1;
        ensures n'.full * 2 == n.full;
        ensures n.full % 2 == 0;
        ensures n'.full == n.full / 2;
    {
        pow2_basics(n);
        assert n.exp - 1 >= 0;
        var m := pow2_t_cons(n.full / 2, n.exp - 1);
        pow2_half_value_lemma(n, m);
        m
    }

    lemma pow2_half_value_lemma(n: pow2_t, n': pow2_t_raw)
        requires n.exp != 0;
        requires n' == pow2_t_cons(n.full / 2, n.exp - 1);
        ensures n'.exp == n.exp - 1;
        ensures n'.full * 2 == n.full
        ensures n'.full == Pow2(n'.exp);
    {
        pow2_basics(n);

        calc == {
            n'.full;
            n.full / 2;
            Pow2(n.exp) / 2;
            {
                reveal Pow();
            }
            Pow2(n.exp - 1);
            Pow2(n'.exp);
        }
    }

    // lemma pow2_square(n: pow2_t) returns (n': pow2_t)
    //     ensures n'.exp == 2 * n.exp 
    //     ensures n'.full == n.full * n.full
    // {
    //     LemmaMulStrictlyPositiveAuto();
    //     var m := pow2_t_cons(n.full * n.full, 2 * n.exp);

    //     calc == {
    //         m.full;
    //         n.full * n.full;
    //         Pow2(n.exp) * Pow2(n.exp);
    //         {
    //             LemmaPowAdds(2, n.exp, n.exp);
    //         }
    //         Pow2(n.exp + n.exp);
    //         Pow2(m.exp);
    //     }

    //     n' := m;
    // }
}