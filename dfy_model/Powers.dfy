include "Congruences.dfy"

module Powers
{
    import opened Congruences

    function method {:opaque} power(b:int, e:nat) : int
        decreases e;
        ensures b > 0 ==> power(b, e) > 0;
        ensures b == 0 && e != 0 ==> power(b, e) == 0;
    {
        if (e == 0) then 1
        else b * power(b, e - 1)
    }

    lemma {:induction e} power_base_one_lemma(e: nat) 
        ensures power(1, e) == 1;
    {
        reveal power();
    }

    lemma {:induction e} power_add_one_lemma(b:int, e:nat)
        ensures power(b, e) * b == power(b, e + 1);
    {
        reveal power();
    }

    lemma {:induction e} power_sub_one_lemma(b:int, e:nat)
        requires e != 0 && b != 0;
        ensures power(b, e) / b == power(b, e - 1);
    {
        assert power(b, e) % b == 0 by {
            power_mod_lemma_1(b, e);
        }
        power_add_one_lemma(b, e - 1);
    }

    lemma {:induction e} power_same_exp_lemma(a: int, b: int, e: nat)
        ensures power(a, e) * power(b, e) == power(a * b, e);
    {
        if e == 0 {
            reveal power();
        } else {
            calc ==> {
                true;
                {
                    power_same_exp_lemma(a, b, e - 1);
                }
                power(a, e - 1) * power(b, e - 1) == power(a * b, e - 1);
                power(a, e - 1) * power(b, e - 1) * a * b == power(a * b, e - 1) * a * b;
                {
                    power_add_one_lemma(a, e - 1);
                    power_add_one_lemma(b, e - 1);
                    power_add_one_lemma(a * b, e - 1);
                }
                power(a, e ) * power(b, e ) == power(a * b, e);
            }
        }
    }

    lemma {:induction e} power_mod_lemma_1(b: int, e: nat) 
        requires e != 0 && b != 0;
        ensures power(b, e) % b == 0;
    {
        reveal power();
        if e != 1 {
            assert power(b, e - 1) % b == 0;
            mod_mul_lemma(power(b, e - 1), b, b);
            assert power(b, e - 1) * b % b == 0;
            power_add_one_lemma(b, e - 1);
            assert power(b, e) % b == 0;
        }
    }

    lemma {:induction e} cong_power_lemma(a: int, b: int, e: nat, n: int)
        requires n != 0;
        requires cong(a, b, n);
        ensures cong(power(a, e), power(b, e), n);
    {
        if e == 0 {
            reveal power();
            reveal cong();
        } else {
            calc ==> {
                cong(a, b, n);
                {
                    cong_power_lemma(a, b, e - 1, n);
                }
                cong(power(a, e - 1), power(b, e - 1), n);
                {
                    cong_mul_lemma_2(power(a, e - 1), power(b, e - 1), a, b, n);
                }
                cong(power(a, e - 1) * a, power(b, e - 1) * b, n);
                {
                    power_add_one_lemma(a, e - 1);
                    power_add_one_lemma(b, e - 1);
                }
                cong(power(a, e), power(b, e), n);
            }
        }
    }
}