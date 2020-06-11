include "Powers.dfy"

module RSAE3v0 {
    import opened Powers

    predicate cong_def(a: int, b: int, n: int)
    {
        exists k : int :: a - b == n * k
    }

    lemma congruent_add_lemma(a: int, b: int, c: int, d: int, n: int)
        requires n != 0;
        requires cong_def(a, b, n) && cong_def(c, d, n)
        ensures cong_def(a + c, b + d, n)
    {
        var k_1, k_2 : int :| a - b == n * k_1 && c - d == n * k_2;
        
        calc == {
            (a + c) - (b + d);
            ==
            (a - b) + (c - d);
            ==
            n * k_1 + n * k_2;
            ==
            (k_1 + k_2) * n;
        }

        ghost var k := (k_1 + k_2);
        assert (a + c) - (b + d) == n * k;
    }

    lemma congruent_sub_lemma(a: int, b: int, c: int, d: int, n: int)
        requires n != 0;
        requires cong_def(a, b, n) && cong_def(c, d, n)
        ensures cong_def(a - c, b - d, n)
    {
        var k_1, k_2 : int :| a - b == n * k_1 && c - d == n * k_2;
        
        calc == {
            (a - c) - (b - d);
            ==
            n * k_1 - n * k_2;
            ==
            (k_1 - k_2) * n;
        }

        ghost var k := (k_1 +- k_2);
        assert (a - c) - (b - d) == n * k;
    }

    lemma residue_congruent_lemma(a: int, b: int, n: int) 
        requires n != 0;
        requires a == b % n;
        ensures cong_def(a, b, n);
    {
        var k := b / n;
        calc ==>
        {
            a + k * n == b;
            a + k * n - b == 0;
            a - b == - k * n;
            a - b == n * (-k);
        }
    }

    lemma residue_smaller_lemma(a: nat, n:nat)
        requires n != 0;
        requires a < n;
        ensures a % n == a;
    {

    }

    lemma mul_distrubtive_lemma(n: int, a: int, b: int, c: int)
        ensures n * (a + b + c) == n * a + n * b  + n * c;
    {
        assert true;
    }

    lemma congruent_mul_lemma(a_1: int, b_1: int, a_2: int, b_2: int, n: int)
        requires cong_def(a_1, b_1, n) && cong_def(a_2, b_2, n);
        ensures cong_def(a_1 * a_2, b_1 * b_2, n);
    {
        ghost var k_1, k_2 : int :| a_1 - b_1 == n * k_1 && a_2 - b_2 == n * k_2;

        calc == {
            a_1 * a_2 - b_1 * b_2;
            ==
            (n * k_1 + b_1) * (n * k_2 + b_2) - b_1 * b_2;
            ==
            n * n * k_1 * k_2 + n * b_1 * k_2 + n * k_1 * b_2;
            ==
            {
                assert n * b_1 * k_2 == n * (b_1 * k_2);
                assert n * k_1 * b_2 == n * (k_1 * b_2);
                assert n * n * k_1 * k_2 == n * (n * k_1 * k_2); // order of these assert somehow matter
            }
            n * (n * k_1 * k_2) + n * (b_1 * k_2) + n * (k_1 * b_2);
            ==
            {
                mul_distrubtive_lemma(n, n * k_1 * k_2, b_1 * k_2, k_1 * b_2);
            }
            n * (n * k_1 * k_2 + b_1 * k_2 + k_1 * b_2);
        }
        ghost var k := n * k_1 * k_2 + b_1 * k_2 + k_1 * b_2;
        assert a_1 * a_2 - b_1 * b_2 == n * k;
        assert cong_def(a_1 * a_2, b_1 * b_2, n);
    }

    lemma congruent_mul_const_lemma(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong_def(a, b, n);
        ensures cong_def(a * c, b * c, n);
    {
        assert cong_def(c, c, n) by {
            congruent_identity_lemma(c, n);
        }
        congruent_mul_lemma(a, b, c, c, n);
    }

    predicate divides_def(d:nat, n:int)
        requires d != 0;
    {
        (n % d) == 0
    }

    predicate gcd_def(a:nat, b:nat, gcd:nat)
    {
        gcd != 0
        && divides_def(gcd,a)
        && divides_def(gcd,b)
        && forall x:int :: gcd < x ==> !(divides_def(x,a) && divides_def(x,b))
    }

    predicate mod_inverse_def(a:int, x:int, n:int)
        requires n != 0;
    {
        (x * a) % n == 1
    }

    function method mod_inverse(a:nat, n:nat) : (x: nat)
        requires n > 0;
        ensures mod_inverse_def(a, x, n);
        ensures x < n;
    {
        assume false;
        42
    }

    predicate montgomery_reduction_def(N: nat, R: nat, T: nat, m: nat)
        requires 0 <= T < N * R;
    {
        (m == (T * mod_inverse(R, N)) % N) && (m < N)
    }

    lemma montgomery_reduction_properties_lemma(N: nat, R: nat, T: nat, m: nat)
        requires 0 <= T < N * R;
        requires montgomery_reduction_def(N, R, T, m);
        ensures cong_def(m, T * mod_inverse(R, N), N);
    {
        ghost var temp := T * mod_inverse(R, N);

        calc ==> {
            m == temp % N;
            m % N == temp % N;
            {
                congruent_mod_connection_sufficient_lemma(m, temp, N);
            }
            cong_def(m, temp, N);
            {
                assert temp == T * mod_inverse(R, N);
            }
            cong_def(m, T * mod_inverse(R, N), N);
        }
    }

    // flaky
    lemma {:induction a} mulitiple_congruent_zero_lemma(a: nat, b: nat)
        requires b != 0;
        ensures cong_def(a * b, 0, b);
    {
        if a == 0 {
            ghost var k := a;
            assert a * b - 0 == b * k;
        } else {
            assert cong_def((a - 1) * b, 0, b);
            ghost var k :| (a - 1) * b == b * k;
            calc == {
                (a * b);
                ==
                (a - 1) * b + b;
                ==
                b * (k + 1);
            }
            ghost var k' := (k + 1);
            assert a * b - 0 == b * k';
        }
    }

    lemma congruent_identity_lemma(a:int, n:int)
        requires n != 0;
        ensures cong_def(a, a, n);
    {
        var k := 0;
        assert a - a == n * k;
    }

    lemma mulitiple_mod_zero_lemma(a: int, b: int)
        requires b != 0;
        ensures (a * b) % b == 0;
    {
        assume false;
    }

    lemma reaminder_mod_lemma(a: nat, b: nat)
        requires b != 0;
        requires a < b;
        ensures a % b == a;
    {
    }

    lemma congruent_mod_connection_sufficient_lemma(a: int, b: int, n: int)
        requires n != 0;
        requires a % n == b % n;
        ensures cong_def(a, b, n);
    {
        var r1 := a % n;
        var k1 := a / n;
        assert a == r1 + k1 * n;

        var r2 := b % n;
        var k2 := b / n;
        assert b == r2 + k2 * n;

        assert r1 == r2;
        calc == {
            a - b;
            == 
            (r1 + k1 * n) - (r2 + k2 * n);
            == 
            k1 * n - k2 * n;
            == 
            (k1 - k2) * n;
        }
        var k := k1 - k2;
        assert a - b == n * k;
    }

    lemma congruent_mod_connection_necessary_lemma(a: int, b: int, n: nat)
        requires n != 0;
        requires cong_def(a, b, n);
        ensures a % n == b % n;
    {
        var r1 := a % n;
        var k1 := a / n;

        assert a == r1 + k1 * n;
        assert r1 == a - k1 * n;
        assert 0 <= r1 < n;
    
        // assert cong_def(a, r1, n) by {
        //     assert a - r1 == n * k1;
        // }
        // var k1' :| a - r1 == n * k1';
        // assert k1' == k1;

        var r2 := b % n;
        var k2 := b / n;

        assert b == r2 + k2 * n;
        assert r2 == b - k2 * n;
        assert 0 <= r2 < n;
    
        // assert cong_def(b, r2, n) by {
        //     assert b - r2 == n * k2;
        // }
        // var k2' :| b - r2 == n * k2';
        // assert k2' == k2;

        var k :| a - b == n * k;

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
                mulitiple_mod_zero_lemma(k + k2 - k1, n);
            }
            0;
        }
        assert r1 == r2;
        assert a % n == b % n;

    }

    lemma congruent_mul_inv_lemma(a: int, b: int, b_inv: int, n: int)
        requires n != 0;
        requires mod_inverse_def(b, b_inv, n);
        ensures cong_def(a, a * b * b_inv, n);
    {
        assert cong_def(a, a * b * b_inv, n) by {
            assert cong_def(1, b * b_inv, n) by {
                calc ==> {
                    1 % n == 1;
                    {
                        assert mod_inverse_def(b, b_inv, n);
                        assert (b * b_inv) % n == 1;
                    }
                    1 % n == (b * b_inv) % n;
                    {
                        congruent_mod_connection_sufficient_lemma(1, b * b_inv, n);
                    }
                    cong_def(1, b * b_inv, n);
                }
            }
            assert cong_def(a, a, n) by {
                congruent_identity_lemma(a, n);
            }
            congruent_mul_lemma(1, b * b_inv, a, a, n);
        }
    }

    lemma congruent_transitivity_lemma(a: int, b: int, c: int, n: nat)
        requires n != 0;
        requires cong_def(a, b, n) && cong_def(b, c, n);
        ensures cong_def(a, c, n);
    {
        assert a % n == b % n by {
            congruent_mod_connection_necessary_lemma(a, b, n);
        }
        assert b % n == c % n by {
            congruent_mod_connection_necessary_lemma(b, c, n);
        }
        assert cong_def(a, c, n) by {
            assert a % n == c % n;
            congruent_mod_connection_sufficient_lemma(a, c, n);
        }
    }

    lemma congruent_reflexivity_lemma(a: int, b: int, n: nat)
        requires n != 0;
        requires cong_def(a, b, n);
        ensures cong_def(b, a, n);
    {
        assert a % n == b % n by {
            congruent_mod_connection_necessary_lemma(a, b, n);
        }
        assert cong_def(b, a, n) by {
            assert b % n == a % n;
            congruent_mod_connection_sufficient_lemma(b, a, n);
        }
    }

    lemma mod_inv_identity_lemma(R: int, R_inv: int, N: nat)
        requires 0 < N < R;
        requires R_inv == mod_inverse(R, N);
        ensures cong_def(R * R_inv, 1, N);
    {
        calc ==> {
            (R * R_inv) % N == 1;
            (R * R_inv) % N == 1 % N;
            {
                congruent_mod_connection_sufficient_lemma(R * R_inv, 1, N);
            }
            cong_def(R * R_inv, 1, N);
        }
    }

    lemma mod_inv_identity_lemma_2(A: int, R: int, R_inv: int, N: nat)
        requires 0 < N < R;
        requires R_inv == mod_inverse(R, N);
        ensures A * R * R_inv % N == A % N;
    {
        assert cong_def(R * R_inv, 1, N) by {
            mod_inv_identity_lemma(R, R_inv, N);
        }
        calc ==> {
            cong_def(R * R_inv, 1, N);
            {
                congruent_mul_const_lemma(R * R_inv, 1, A, N);
            }
            cong_def(A * R * R_inv, A, N);
            {
                congruent_mod_connection_necessary_lemma(A * R * R_inv, A, N);
            }
            A * R * R_inv % N == A % N;
        }
    }

    lemma montgomery_reduction_sufficient_lemma(N: nat, R: nat, T: nat, t: nat)
        requires gcd_def(N, R, 1);
        requires 0 <= T < N * R;
        requires (t * R) % N == T % N;
        requires t < N;
        ensures montgomery_reduction_def(N, R, T, t);
    {
        var R_inv := mod_inverse(R, N);
        var m := (T * R_inv) % N;

        assert cong_def(t * R, T, N) by {
            assert (t * R) % N == T % N;
            congruent_mod_connection_sufficient_lemma(t * R, T, N);
        }

        assert cong_def(R_inv, R_inv, N) by {
            congruent_identity_lemma(R_inv, N); 
        }

        calc ==> {
            cong_def(t * R, T, N) && cong_def(R_inv, R_inv, N);
            {
                congruent_mul_lemma(t * R, T, R_inv, R_inv, N);
            }
            cong_def(t * R * R_inv, T * R_inv, N);
            {
                assert cong_def(t, t * R * R_inv, N) by {
                    congruent_mul_inv_lemma(t, R, R_inv, N);
                }
                assert cong_def(t, T * R_inv, N) by {
                    congruent_transitivity_lemma(t, t * R * R_inv, T * R_inv, N);
                }
            }
            cong_def(t, T * R_inv, N);
        }
        
        assert cong_def(t, T * R_inv, N);
        assert t % N == (T * R_inv) % N by {
            congruent_mod_connection_necessary_lemma(t, T * R_inv, N);
        }

        calc == {
            t % N - (T * R_inv) % N;
            ==
            {
                reaminder_mod_lemma(t, N);
                assert t % N == t;
            }
            t - (T * R_inv) % N;
        }

        assert montgomery_reduction_def(N, R, T, t);
    }

    lemma reduction_bounded_lemma(N: nat, R: nat, T: int, m: nat, t: int)
        requires N != 0 && R != 0;
        requires 0 <= m < R;
        requires 0 <= T < (N * R);
        requires t == (T + m * N) / R;
        ensures 0 <= t < 2 * N;
    {
        calc ==> {
            0 <= m < R;
            {
                assert N > 0;
            }
            0 <= m * N < R * N;
            {
                assert 0 <= T < (N * R);
            }
            0 <= T + m * N < T + R * N;
            {
                assert 0 <= T < (N * R);
            }
            0 <= T + m * N < N * R + R * N;
            {
                assert N * R + R * N == 2 * N * R; 
            }
            0 <= T + m * N < 2 * N * R;
            {
                assert R > 0;
            }
            0 <= (T + m * N) / R < 2 * N;
            {
                assert t == (T + m * N) / R;
            }
            0 <= t < 2 * N;
        }     
    }

    lemma reduction_divisibie_lemma(N: nat, N': int, R: nat, T: int, m: int)
        requires N != 0 && R != 0;
        requires gcd_def(N, R, 1);
        requires 0 <= T < (N * R);
        requires m == (T * N') % R;
        requires cong_def(N' * N, -1, R);
        ensures (T + m * N) % R == 0; 
    {
        assert cong_def(m, T * N', R) by {
            assert m % R == (T * N') % R;
            congruent_mod_connection_sufficient_lemma(m, T * N', R);
        }

        assert cong_def(N, N, R) by {
            congruent_identity_lemma(N, R);
        }

        calc ==> {
            cong_def(m, T * N', R) && cong_def(N, N, R);
            {
                congruent_mul_lemma(m, T * N', N, N, R);
                assert cong_def(m * N, N * T * N', R);
            }
            cong_def(m * N, N * T * N', R);
            {
                assert N * T * N' == N' * N * T;
            }
            cong_def(m * N, N' * N * T, R);
        }

        calc ==> {
            cong_def(N' * N, -1, R);
            {
                assert cong_def(T, T, R);
                congruent_mul_lemma(N' * N, -1, T, T, R);
            }
            cong_def(N' * N * T, -1 * T, R);
            {
                assert -1 * T == -T;
            }
            cong_def(N' * N * T, -T, R);
        }

        calc ==> {
            cong_def(m * N, N' * T * N, R) && cong_def(N' * N * T, -T, R);
            {
                congruent_transitivity_lemma(m * N, N' * N * T, -T, R);
            }
            cong_def(m * N, -T, R);
            {
                assert cong_def(T, T, R);
                congruent_add_lemma(m * N, -T, T, T, R);
            }
            cong_def(m * N + T, -T + T, R);
            {
                assert -T + T == 0;
                assert m * N + T == T + m * N;
            }
            cong_def(T + m * N, 0, R);
            {
                congruent_mod_connection_necessary_lemma(T + m * N, 0, R);
            }
            (T + m * N) % R == 0 % R; 
            (T + m * N) % R == 0; 
        }
        assert (T + m * N) % R == 0; 
    }

    lemma reduction_congruent_lemma(N: nat, R: nat, T: int, t: int, t': int)
        requires N != 0 && R != 0;
        requires cong_def(t * R, T, N);
        requires t' == t - N;
        ensures cong_def(t' * R, T, N);
    {
        assert cong_def(N * R, 0, N) by {
            mulitiple_congruent_zero_lemma(N, R);
        }

        ghost var a, d := t * R, 0;

        assert cong_def(a, T, N);
        assert cong_def(N * R, d, N);

        calc ==> {
            cong_def(a, T, N) && cong_def(N * R, d, N);
            {
                congruent_sub_lemma(a, T, N * R, d, N);
            }
            cong_def(a - N * R, T - d, N);
            {
                assert N - d == N;
            }
            cong_def(a - N * R, T, N);
            {
                assert a == t * R;
            }
            cong_def(t * R - N * R, T, N);
            {
                assert t * R - N * R == (t - N) * R;
            }
            cong_def((t - N) * R, T, N);
            {
                assert t' == t - N;
            }
            cong_def(t' * R, T, N);
        }
        assert cong_def(t' * R, T, N);
    }

    method montgomery_reduction(N: nat, R: nat, T: int) returns (t: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires 0 <= T < (N * R);
        ensures montgomery_reduction_def(N, R, T, t);
    {
        var N_inv := mod_inverse(N, R);
        var N' := R - N_inv;

        assert cong_def(N * R - N_inv * N, -1, R) by {
            assert cong_def(N_inv * N, 1, R) by {
                calc ==> {
                    (N_inv * N) % R == 1;
                    (N_inv * N) % R == 1 % R;
                    {
                        congruent_mod_connection_sufficient_lemma(N_inv * N, 1, R);
                    }
                    cong_def(N_inv * N, 1, R);
                }
            }
            assert cong_def(N * R, 0, R) by {
                mulitiple_congruent_zero_lemma(N, R);
            }
            congruent_sub_lemma(N * R, 0, N_inv * N, 1, R);
        }

        calc ==> {
            cong_def(N * R - N_inv * N, -1, R);
            {
                assert N * R - N_inv * N == N * (R - N_inv);
            }
            cong_def(N * (R - N_inv), -1, R);
            {
                assert N' == R - N_inv;
            }
            cong_def(N * N', -1, R);
        }

        assert cong_def(N' * N, -1, R);

        var m := (T * N') % R;        

        assert (T + m * N) % R == 0 by {
            reduction_divisibie_lemma(N, N', R, T, m);
        }

        t := (T + m * N) / R;

        assert 0 <= t < 2 * N by {
            reduction_bounded_lemma(N, R, T, m, t);
        }

        assert cong_def(t * R, T, N) by {
            assert t * R - T == N * m;
        }

        if t >= N {
            var t' := t - N;
            assert 0 <= t' < N;
            assert cong_def(t' * R, T, N) by {
                reduction_congruent_lemma(N, R, T, t, t');
            }
            t := t';
            assert 0 <= t < N;
            assert cong_def(t * R, T, N);
        }
        assert 0 <= t < N;

        assert (t * R) % N == T % N by {
            assert cong_def(t * R, T, N);
            congruent_mod_connection_necessary_lemma(t * R, T, N);
        }

        assert montgomery_reduction_def(N, R, T, t) by {
            montgomery_reduction_sufficient_lemma(N, R, T, t);
        }
    }

    lemma montgomery_representation_lemma(a: nat, a': nat, R: nat, R_inv: nat, N: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires R_inv == mod_inverse(R, N);
        requires cong_def(a', a * R, N);
        ensures cong_def(a' * R_inv, a, N);
    {
        calc ==> {
            cong_def(a', a * R, N);
            {
                congruent_mul_const_lemma(a', a * R, R_inv, N);
            }
            cong_def(a' * R_inv, a * R * R_inv, N);
            {
                assert cong_def(R * R_inv, 1, N) by {
                    mod_inv_identity_lemma(R, R_inv, N);
                }
                calc ==>
                {
                    cong_def(R * R_inv, 1, N);
                    {
                        congruent_mul_const_lemma(R * R_inv, 1, a, N);
                    }
                    cong_def(R * R_inv * a, a, N);
                    {
                       assert a * R * R_inv == R * R_inv * a;
                    }
                    cong_def(a * R * R_inv, a, N);
                }
                assert cong_def(a' * R_inv, a, N) by {
                    congruent_transitivity_lemma(a' * R_inv, a * R * R_inv, a, N);
                }
            }
            cong_def(a' * R_inv, a, N);
        }
    }

    lemma montgomery_mod_mul_lemma(a: nat, b: nat, c: nat, a': nat, b': nat,  c': nat, R: nat, R_inv: nat, N: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires R_inv == mod_inverse(R, N);
        requires cong_def(c', (a' * b') * R_inv, N);
        requires cong_def(c, c' * R_inv, N);
        requires cong_def(a', a * R, N);
        requires cong_def(b', b * R, N);
        ensures cong_def(c, a * b, N);
    {
        calc ==> {
            cong_def(c', (a' * b') * R_inv, N);
            {
                congruent_mul_const_lemma(c', (a' * b') * R_inv, R_inv, N);
            }
            cong_def(c' * R_inv, (a' * b') * R_inv * R_inv, N);
            {
                assert cong_def(c, c' * R_inv, N);
                congruent_transitivity_lemma(c, c' * R_inv, (a' * b') * R_inv * R_inv, N); 
            }
            cong_def(c, (a' * b') * R_inv * R_inv, N);
            {
                assert a' * R_inv * b' * R_inv == (a' * b') * R_inv * R_inv;
            }
            cong_def(c, a' * R_inv * b' * R_inv, N);
        }

        assert cong_def(c, a * b, N) by {
            assert cong_def(a' * R_inv * b' * R_inv, a * b, N) by {
                assert cong_def(a' * R_inv, a, N) by {
                    montgomery_representation_lemma(a, a', R, R_inv, N);
                }
                assert cong_def(b' * R_inv, b, N) by {
                    montgomery_representation_lemma(b, b', R, R_inv, N);
                }
                congruent_mul_lemma(a' * R_inv, a, b' * R_inv, b, N);
            }
            assert cong_def(c, a' * R_inv * b' * R_inv, N);
            congruent_transitivity_lemma(c, a' * R_inv * b' * R_inv, a * b, N); 
        }
    }

    method mul_mod_montgomery(a: nat, b: nat, N:nat, R: nat) returns (c: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        ensures c == (a * b) % N;
    {
        var a' := (a * R) % N;
        var b' := (b * R) % N;
        assert a' < N && b' < N;
        assert a' * b' < N * N;

        ghost var R_inv := mod_inverse(R, N);

        var c' := montgomery_reduction(N, R, a' * b');
        c := montgomery_reduction(N, R, c');

        assert cong_def(c, a * b, N) by {
            assert cong_def(a', a * R, N) by {
                assert a' == (a * R) % N;
                residue_congruent_lemma(a', a * R, N);
            }

            assert cong_def(b', b * R, N) by {
                assert b' == (b * R) % N;
                residue_congruent_lemma(b', b * R, N);
            }
            assert cong_def(c', (a' * b') * R_inv, N) by {
                assert montgomery_reduction_def(N, R, a' * b', c');
                montgomery_reduction_properties_lemma(N, R, a' * b', c');
            }

            assert cong_def(c, c' * R_inv, N) by {
                assert montgomery_reduction_def(N, R, c', c);
                montgomery_reduction_properties_lemma(N, R, c', c);
            }

            montgomery_mod_mul_lemma(a, b, c, a', b', c', R, R_inv, N);
        }

        assert c % N == (a * b) % N by {
            congruent_mod_connection_necessary_lemma(c, a * b, N);
        }

        assert c % N == c by {
            residue_smaller_lemma(c, N);
        }

        assert c == (a * b) % N;
    }

    lemma not_so_interesting_lemma(a: int, b: int, c: int, n: nat)
        requires n != 0;
        requires a == b % n;
        ensures (a * c) % n == (b * c) % n;
    {
        ghost var d := (b * c) % n;
        assert cong_def(a, b, n) by {
            residue_congruent_lemma(a, b, n);
        }
        assert cong_def(a * c, b * c, n) by {
            congruent_mul_const_lemma(a, b, c, n);
        }
        assert a * c % n == b * c % n by {
            congruent_mod_connection_necessary_lemma(a * c, b * c, n);
        }
    }

    lemma not_so_interesting_lemma_2(a: int, b: int, n: nat)
        requires n != 0;
        ensures ((a % n) * b) % n == (a * b) % n;
    {
        not_so_interesting_lemma(a % n, a, b, n);
    }

    lemma power_exp_lemma(a: nat, b: nat, n: nat)
        requires n != 0;
        ensures power(a, b) % n == power(a % n, b) % n;
    {
        assume false;
    }

    method montgomery_product(A: nat, B: nat, N:nat, R: nat, R_inv: nat) returns (P: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires R_inv == mod_inverse(R, N);
        // requires cong_def(N' * N, -1, R);
        ensures P == A * B * R_inv % N;
    {
        var N_inv := mod_inverse(N, R);
        var N';
        assume(cong_def(N' * N_inv, R - 1, R));

        var T := A * B;
        var M := T * N' % R;
        P := (T + M * N) / R;

        assume false;
    }

    lemma multiplication_para(a: int, b: int, c: int, d: int)
        ensures (a * b) * (c * d) == (a * c) * (b * d);
    {
        assert true;
    }

    lemma montgomery_reapeat_product_lemma(C': nat, C'': nat, M': nat, E: nat, N:nat, R: nat, R_inv: nat, i: nat)
        requires i != 0;
        requires 0 < N < R && gcd_def(N, R, 1);
        requires C' == power(M', i) * power(R_inv, i - 1) % N;
        requires C'' == (C' * M' * R_inv) % N;
        ensures C'' == (power(M', i + 1) * power(R_inv, i)) % N;
    {
        ghost var P0 := power(M', i) * power(R_inv, i - 1);
        ghost var P1 := M' * R_inv;

        calc == {
            C'';
            ==
            (C' * M' * R_inv) % N;
            ==
            {
                assert C' == power(M', i) * power(R_inv, i - 1) % N;
            }
            ((power(M', i) * power(R_inv, i - 1) % N) * M' * R_inv) % N;
            ==
            {
                assert P0 == power(M', i) * power(R_inv, i - 1);
            }
            ((P0 % N) * (M' * R_inv)) % N;
            ==
            {
                assert P1 == M' * R_inv;
            }
            ((P0 % N) * P1) % N;
            ==
            {
                not_so_interesting_lemma_2(P0, P1, N);
            }
            (P0 * P1) % N;
            ==
            {
                assert P0 == power(M', i) * power(R_inv, i - 1);
            }
            ((power(M', i) * power(R_inv, i - 1)) * P1) % N;
            ==
            {
                assert P1 == M' * R_inv;
            }
            ((power(M', i) * power(R_inv, i - 1)) * (M' * R_inv)) % N;
            ==
            {
                assert (power(M', i) * power(R_inv, i - 1)) * (M' * R_inv)
                    == (power(M', i) * M') * (power(R_inv, i - 1) * R_inv) by {
                    multiplication_para(power(M', i), power(R_inv, i - 1), M', R_inv);
                }
            }
            ((power(M', i) * M') * (power(R_inv, i - 1) * R_inv)) % N;
            {
                assert (power(M', i) * M') == power(M', i + 1) by {
                    power_add_one_lemma(M', i); 
                }
            }
            (power(M', i + 1) * (power(R_inv, i - 1) * R_inv)) % N;
            {
                assert power(R_inv, i - 1) * R_inv == power(R_inv, i) by {
                    power_add_one_lemma(R_inv, i - 1); 
                }
            }
            (power(M', i + 1) * power(R_inv, i)) % N;
        }
        assert C'' == (power(M', i + 1) * power(R_inv, i)) % N;
    }

    lemma montgomery_exp_lemma(M: nat, M': nat, E: nat, N:nat, R: nat, R_inv: nat, C: nat, C': nat)
        requires E > 1;
        requires 0 < N < R && gcd_def(N, R, 1);
        requires M' == (M * R) % N;
        requires R_inv == mod_inverse(R, N);
        requires C' == power(M', E) * power(R_inv, E - 1) % N;
        requires montgomery_reduction_def(N, R, C', C);
        ensures C == power(M, E) % N;
    {
        calc == {
            C;
            ==
            {
                assert montgomery_reduction_def(N, R, C', C);
            }
            C' * mod_inverse(R, N) % N;
            ==
            C' * R_inv % N;
            ==
            {
                assert C' == power(M', E) * power(R_inv, E - 1) % N;
            }
            (power(M', E) * power(R_inv, E - 1) % N) * R_inv % N;
            ==
            {
                not_so_interesting_lemma_2(power(M', E) * power(R_inv, E - 1), R_inv, N);
            }
            (power(M', E) * power(R_inv, E - 1)) * R_inv % N;
            ==
            power(M', E) * power(R_inv, E - 1) * R_inv % N;
            ==
            power(M', E) * (power(R_inv, E - 1) * R_inv) % N;
            ==
            (power(R_inv, E - 1) * R_inv) * power(M', E) % N; // if we don't reoder, the parse tree gets messed up, takes forever to prove 
            ==
            {
                assert(power(R_inv, E - 1) * R_inv) == power(R_inv, E) by {
                    power_add_one_lemma(R_inv, E - 1);
                }
            }
            power(R_inv, E) * power(M', E) % N;
            ==
            {
                power_same_exp_lemma(R_inv, M', E);
            }
            power(M' * R_inv, E) % N;
            ==
            {
                power_exp_lemma(M' * R_inv, E, N);
            }
            power(M' * R_inv % N, E) % N;
            ==
            power((M' * R_inv % N), E) % N;
            ==
            {
                ghost var a := (M * R);
                calc == {
                    M' * R_inv % N;
                    ==
                    {
                        assert M' == a % N;
                    }
                    (a % N * R_inv) % N;
                    ==
                    {
                        not_so_interesting_lemma_2(a, R_inv, N);
                    }
                    (a * R_inv) % N;
                    ==
                    (M * R * R_inv) % N;
                    ==
                    {
                        mod_inv_identity_lemma_2(M, R, R_inv, N );
                    }
                    M % N;
                }
                assert (M' * R_inv % N) == M % N;
            }
            power(M % N, E) % N;
            ==
            {
                power_exp_lemma(M, E, N);
            }
            power(M, E) % N;
        }
        assert C == power(M, E) % N;
    }

    method exp_mod_montgomery(M: nat, E: nat, N:nat, R: nat, R_inv: nat) returns (C: nat)
        requires E > 1;
        requires 0 < N < R && gcd_def(N, R, 1);
        requires R_inv == mod_inverse(R, N);
        ensures C == power(M, E) % N;
    {
        var M' : nat := (M * R) % N;
        var C' : nat := M';
    
        var i :nat := 1;

        assert C' == power(M', i) * power(R_inv, i - 1) % N by {
            reveal power();
        }

        while i < E
            invariant C' == power(M', i) * power(R_inv, i - 1) % N;
            invariant i <= E;
            decreases E - i;
        {
            var C'' := montgomery_product(C', M', N, R, R_inv);

            assert C'' == power(M', i + 1) * power(R_inv, i) % N by {
                montgomery_reapeat_product_lemma(C', C'', M', E, N, R, R_inv, i);
            }

            i := i + 1;
            assert C'' == power(M', i) * power(R_inv, i - 1) % N;
            C' := C'';
            assert C' == power(M', i) * power(R_inv, i - 1) % N;
        }

        assert i == E;
        assert C' == power(M', E) * power(R_inv, E - 1) % N;

        C := montgomery_reduction(N, R, C');

        assert C == power(M, E) % N by {
            montgomery_exp_lemma(M, M', E, N, R, R_inv, C, C');
        }
    }
}