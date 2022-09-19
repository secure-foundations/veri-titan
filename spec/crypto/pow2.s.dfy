include "../../std_lib/src/NonlinearArithmetic/Power2.dfy"
include "../../std_lib/src/NonlinearArithmetic/DivMod.dfy"
include "../../std_lib/src/Collections/Sequences/Seq.dfy"

module pow2_s {
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul

    datatype pow2_t_raw = pow2_t_cons(full: nat, exp: nat)

    type pow2_t = n: pow2_t_raw | n.full == Pow2(n.exp) witness *

    function method pow2(exp: nat): pow2_t
    {
        LemmaPowPositiveAuto();
        reveal Pow2();
        pow2_t_cons(Pow(2, exp), exp)
    }

    lemma pow2_basics_lemma(n: pow2_t)
        ensures n.exp == 0 <==> n.full == 1
        ensures n.exp == 1 <==> n.full == 2
        ensures n.exp != 0 ==> n.full % 2 == 0
        ensures n.full >= 1
    {
        reveal Pow();
        reveal Pow2();
        if n.full == 2 && n.exp != 1{
            assert n.exp != 0;
            assert n.exp > 1;
            LemmaPowStrictlyIncreases(2, 1, n.exp);
        }
        LemmaPowPositiveAuto();
    }

    lemma pow2_increases_lemma(n: pow2_t, n': pow2_t)
        ensures n.exp < n'.exp <==> n.full < n'.full;
    {
        reveal Pow2();
        if n.exp < n'.exp {
            LemmaPowStrictlyIncreases(2, n.exp, n'.exp);
        }
        if n.full < n'.full {
            LemmaPowStrictlyIncreasesConverse(2, n.exp, n'.exp);
        }
    }

    lemma pow2_half_value_lemma(n: pow2_t, n': pow2_t_raw)
        requires n.exp != 0;
        requires n' == pow2_t_cons(n.full / 2, n.exp - 1);
        ensures n'.exp == n.exp - 1;
        ensures n'.full * 2 == n.full
        ensures n'.full == Pow2(n'.exp);
    {
        pow2_basics_lemma(n);

        calc == {
            n'.full;
            n.full / 2;
            Pow2(n.exp) / 2;
            {
                reveal Pow2();
                reveal Pow();
            }
            Pow2(n.exp - 1);
            Pow2(n'.exp);
        }
    }

    function method pow2_half(n: pow2_t) : (n': pow2_t)
        requires n.exp != 0 || n.full != 1;
        ensures n'.exp == n.exp - 1;
        ensures n'.full * 2 == n.full;
        ensures n.full % 2 == 0;
        ensures n'.full == n.full / 2;
    {
        pow2_basics_lemma(n);
        assert n.exp - 1 >= 0;
        var m := pow2_t_cons(n.full / 2, n.exp - 1);
        pow2_half_value_lemma(n, m);
        m
    }

    function method pow2_double(n: pow2_t) : (n': pow2_t)
        ensures n'.exp == n.exp + 1;
        ensures n'.full == n.full * 2;
    {
        pow2_basics_lemma(n);
        reveal Pow2();
        reveal Pow();
        var m := pow2_t_cons(n.full * 2, n.exp + 1);
        m
    }

    function method pow2_mul(n: pow2_t, m: pow2_t) : (n': pow2_t)
    {
        LemmaPowAdds(2, n.exp, m.exp);
        LemmaMulStrictlyPositiveAuto();
        reveal Pow2();
        var a := pow2_t_cons(n.full * m.full, n.exp + m.exp);
        a
    }

    function method pow2_div(n: pow2_t, m: pow2_t) : (n': pow2_t)
        requires m.exp <= n.exp;
        ensures m.full != 0;
        ensures n.full % m.full == 0;
        ensures n.full == n'.full * m.full;
    {
        pow2_basics_lemma(m);
        pow2_basics_lemma(n);
        LemmaPowSubtracts(2, m.exp, n.exp);
        reveal Pow2();
        var a := pow2_t_cons(n.full / m.full, n.exp - m.exp);
        assert n == pow2_mul(m, a);
        assert n.full == a.full * m.full;
        LemmaFundamentalDivMod(n.full, m.full);
        a
    }
}
