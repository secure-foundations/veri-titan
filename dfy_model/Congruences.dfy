module Congruences {
    predicate {:opaque} cong(a: int, b: int, n: int)
        requires n != 0;
    {
        a % n == b % n
    }

    lemma cong_equiv_lemma(a: int, b: int, n: int)
        requires n != 0;
        ensures cong(a, b, n) <==> ((a - b) % n == 0);
    {
        var k1, k2 := a / n, b / n;
        assert k1 * n + a % n == a;
        assert k2 * n + b % n == b;

        if cong(a, b, n) {
            reveal cong();
            calc == {
                (a - b) % n;
                (k1 * n + a % n - k2 * n - b % n) % n;
                (k1 * n - k2 * n) % n;
                ((k1 - k2) * n) % n;
                {
                    mod_mul_lemma(k1 - k2, n, n);
                }
                0;
            }
            assert cong(a, b, n) ==> (a - b) % n == 0;
        }

        if (a - b) % n == 0 {
            var k := (a - b) / n;
            assert k * n == a - b;
            var r1, r2 := a % n, b % n;

            calc == {
                (r1 - r2) % n;
                ==
                {
                    calc == {
                        r1 - r2;
                        ==
                        (a - k1 * n) - (b - k2 * n);
                        ==
                        (a - b) + (k2 - k1) * n;
                        ==
                        n * k + (k2 - k1) * n;
                        ==
                        (k + k2 - k1) * n;
                    }
                }
                ((k + k2 - k1) * n) % n;
                ==
                {
                    mod_mul_lemma(k + k2 - k1, n, n);
                }
                0;
            }
            assert r1 == r2;
            assert a % n == b % n;
            reveal cong();
            assert cong(a, b, n) <== ((a - b) % n == 0);
        }
    }

    lemma cong_remainder_lemma(a: int, b:int, n: int)
        requires n != 0;
        requires cong(a, b, n) && 0 <= a < n;
        ensures a == b % n;
    {
        reveal cong();
        assert a % n == a;
    }

    lemma mod_div_inv_leamma(a: int, b: int, b_inv: int, n: int)
        requires n != 0 && b != 0
        requires cong(b * b_inv, 1, n);
        requires a % b == 0;
        ensures cong(a * b_inv, a / b, n);
    {
        assert cong(a / b, a / b, n) by {
            reveal cong();
        }

        calc ==> {
            cong(a / b, a / b, n);
            {
                cong_mul_lemma_1(a / b, a / b, b * b_inv, n);
            }
            cong(a * b_inv,  (a / b) * b_inv * b, n);
            {
                assert cong((a / b) * b * b_inv, a / b, n) by {
                    assert cong(b * b_inv, 1, n);
                    cong_mul_lemma_1(b * b_inv, 1, a / b, n);
                }
                assert cong(a * b_inv, a / b, n) by {
                    cong_trans_lemma(a * b_inv,  (a / b) * b_inv * b, a / b, n);
                } 
            }
            cong(a * b_inv, a / b, n);
        }
    }

    lemma cong_trans_lemma(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires (cong(a, b, n) || cong(b, a, n)) && (cong(b, c, n) || cong(c, b, n));
        ensures cong(a, c, n);
    {
        reveal cong();
    }

    lemma cong_residual_lemma(a: int, b: nat, n: nat)
        requires n != 0;
        ensures (cong(a, b, n) && b < n) <==> (b == a % n);
    {
        reveal cong();        
    }

    lemma cong_mod_lemma(a: int, n: int)
        requires n != 0;
        ensures cong((a % n), a, n);
    {
        reveal cong();
    }

    lemma mod_mul_lemma(a: int, b: int, n: int)
        requires n != 0;
        requires b % n == 0;
        ensures a * b % n == 0;
    {
        assume false;
    }

    lemma cong_mul_lemma_1(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong(a, b, n);
        ensures cong(a * c, b * c, n);
    {
        ghost var k1, k2 := a / n, b / n;
        assert k1 * n + a % n == a;
        assert k2 * n + b % n == b;

        assert (a - b) % n == 0 by {
            cong_equiv_lemma(a, b, n);
        }

        calc == {
            a * c - b * c;
            (k1 * n + a % n) * c - (k2 * n + b % n) * c;
            {
                assert a % n * c == b % n * c by {
                    reveal cong();
                }
            }
            k1 * n * c - k2 * n * c;
            (k1 - k2) * n * c;
            (k1 - k2) * c * n;
        }

        ghost var temp := (k1 - k2) * c; 

        calc == {
            (a * c - b * c) % n;
            (temp * n) % n;
            {
                mod_mul_lemma(temp, n, n);
            }
            0;
        }
        assert (a * c - b * c) % n == 0;
        cong_equiv_lemma(a * c, b * c, n);
    }

    lemma cong_mul_lemma_2(a: int, b: int, c: int, d: int, n: int)
        requires n != 0;
        requires cong(a, b, n) && cong(c, d, n);
        ensures cong(a * c, b * d, n);
    {
        ghost var k1, k2, k3, k4 := a / n, b / n, c / n, d / n;
        ghost var r1, r2, r3, r4 := a % n, b % n, c % n, d % n;

        assert r1 == r2 && r3 == r4 by {
            reveal cong();
        }

        calc == {
            a * c - b * d;
            (k1 * n + r1) * (k3 * n + r3) - (k2 * n + r1) * (k4 * n + r3);
            (k1 * n + r1) * k3 * n + (k1 * n + r1) * r3 - (k2 * n + r1) * k4 * n - (k2 * n + r1) * r3;
            ((k1 * n + r1) * k3 - (k2 * n + r1) * k4) * n + (k1 * n + r1) * r3 - (k2 * n + r1) * r3;
            ((k1 * n + r1) * k3 - (k2 * n + r1) * k4) * n + k1 * n * r3 + r1 * r3 - k2 * n * r3 - r1 * r3;
            ((k1 * n + r1) * k3 - (k2 * n + r1) * k4) * n + k1 * n * r3 - k2 * n * r3;
            ((k1 * n + r1) * k3 - (k2 * n + r1) * k4) * n + (k1 * r3 - k2 * r3) * n;
            ((k1 * n + r1) * k3 - (k2 * n + r1) * k4 + k1 * r3 - k2 * r3) * n;
        }
        var temp := (k1 * n + r1) * k3 - (k2 * n + r1) * k4 + k1 * r3 - k2 * r3;

        calc ==> {
            n % n == 0;
            {
                mod_mul_lemma(temp, n, n);
            }
            (temp * n) % n == 0;
            {
                assert a * c - b * d == temp * n;
            }
            (a * c - b * d) % n == 0;
            {
                cong_equiv_lemma(a * c, b * d, n);
            }
            cong(a * c, b * d, n);
        }        
    }

    lemma cong_add_lemma_1(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong(a, b, n);
        ensures cong(a + c, b + c, n);
    {
        reveal cong();
        cong_add_lemma_2(a, b, c, c, n);
    }

    lemma cong_add_lemma_2(a: int, b: int, c: int, d: int, n: int)
        requires n != 0;
        requires cong(a, b, n) && cong(c, d, n);
        ensures cong(a + c, b + d, n);
    {
        ghost var k1, k2, k3, k4 := a / n, b / n, c / n, d / n;
        ghost var r1, r2, r3, r4 := a % n, b % n, c % n, d % n;

        assert r1 == r2 && r3 == r4 by {
            reveal cong();
        }

        calc == {
            a + c - b - d;
            k1 * n + k3 * n - k2 * n - k4 * n;
            (k1 + k3 - k2 - k4) * n;
        }

        assert (k1 + k3 - k2 - k4) * n % n == 0 by {
            mod_mul_lemma(k1 + k3 - k2 - k4, n, n);
        }
        
        assert (a + c - b - d) % n == 0;
        cong_equiv_lemma(a + c,  b + d, n);
    }
    
    lemma cong_add_lemma_3(a: int, m: int, n: int)
        requires n != 0;
        requires m % n == 0;
        ensures cong(a, a + m, n);
    {
        reveal cong();
        cong_add_lemma_2(a, a, 0, m, n);
    }
}
