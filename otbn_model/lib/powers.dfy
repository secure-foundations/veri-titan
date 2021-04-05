include "congruences.dfy"

module powers
{
    import opened congruences

    function method {:opaque} power(b: int, e: nat) : int
        decreases e;
        ensures b > 0 ==> power(b, e) > 0;
        ensures b == 0 && e != 0 ==> power(b, e) == 0;
    {
        if (e == 0) then 1
        else b * power(b, e - 1)
    }

    function {:opaque} pow2(e: nat) : (r : nat)
        ensures r != 0;
    {
		if e == 0 then 1 else 2 * pow2(e - 1)
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

    lemma {:induction e2} power_same_base_lemma(a: int, e1: nat, e2: nat)
        ensures power(a, e1) * power(a, e2) == power(a, e1 + e2);
    {
        if e2 == 0 {
            reveal power();
        } else {
            calc ==> {
                true;
                {
                    power_same_base_lemma(a, e1, e2 - 1);
                }
                power(a, e1) * power(a, e2 - 1) == power(a, e1 + e2 - 1);
                power(a, e1) * power(a, e2 - 1) * a == power(a, e1 + e2 - 1) * a;
                {
                    assert power(a, e2 - 1) * a == power(a, e2) by {
                        power_add_one_lemma(a, e2 - 1);
                    }
                }
                power(a, e1) * power(a, e2) == power(a, e1 + e2 - 1) * a;
                {
                    assert power(a, e1 + e2 - 1) * a == power(a, e1 + e2) by {
                        power_add_one_lemma(a, e1 + e2 - 1);
                    }
                }
                power(a, e1) * power(a, e2) == power(a, e1 + e2);
            }
            assert power(a, e1) * power(a, e2) == power(a, e1 + e2);
        }
    }

    lemma {:inudction e2} power_power_lemma(b: int, e1: nat, e2: nat)
        ensures power(power(b, e1), e2) == power(b, e1 * e2);
    {
        if e2 == 0 {
            reveal power();
        } else {
            assert power(power(b, e1), e2 - 1) == power(b, e1 * (e2 - 1)) by {
                power_power_lemma(b, e1, e2 - 1);
            }

            assert power(power(b, e1), e2 - 1) * power(b, e1) == power(power(b, e1), e2) by {
                power_add_one_lemma(power(b, e1), e2 - 1);
            }

            assert power(b, e1 * (e2 - 1)) * power(b, e1) == power(b, e1 * e2) by {
                power_same_base_lemma(b,  e1 * (e2 - 1), e1);
                assert e1 * (e2 - 1) + e1 == e1 * e2;
            }
        }
    }

    lemma {:induction e} power_mod_lemma_2(b: int, e: nat, n: int)
        requires n != 0;
        ensures power(b % n, e) % n == power(b, e) % n;
    {
        if e == 0 {
            reveal power();
        } else {
            calc ==> {
                true;
                {
                    power_mod_lemma_2(b, e - 1, n);
                }
                power(b % n, e - 1) % n == power(b, e - 1) % n;
                {
                    reveal cong();
                }                
                cong(power(b % n, e - 1), power(b, e - 1), n);
                {
                    assert cong(b % n, b, n) by {
                        reveal cong();
                    }
                    cong_mul_lemma_2(power(b % n, e - 1), power(b, e - 1), b % n, b, n);
                }
                cong(power(b % n, e - 1) * (b % n), power(b, e - 1) * b, n);
                {
                    power_add_one_lemma(b % n, e - 1);
                }
                cong(power(b % n, e), power(b, e - 1) * b, n);
                {
                    power_add_one_lemma(b, e - 1);
                }
                cong(power(b % n, e), power(b, e), n);
            }

            assert power(b % n, e) % n == power(b, e) % n by {
                assert cong(power(b % n, e), power(b, e), n);
                reveal cong();
            }
        }
    }
}