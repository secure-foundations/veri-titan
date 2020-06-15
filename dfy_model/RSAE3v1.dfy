include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"
include "SeqInt.dfy"

module RSAE3v1 {
    import opened NativeTypes
    import opened Powers
    import opened Congruences
    import opened SeqInt

    method mont_mul(m: seq<uint32>, x: seq<uint32>, y: seq<uint32>, m': uint32, n: nat, ghost R: int, ghost BASE_INV: nat)
        returns (A: seq<uint32>)

        requires n > 2;
        requires |m| == n && |x| == n && |y| == n;
        requires R == power(BASE, n);
        requires cong(m' as int * sint(m), -1, BASE);
        requires 0 <= sint(x) < sint(m); 
        requires 0 <= sint(y) < sint(m); 
        requires cong(BASE * BASE_INV, 1, sint(m));

        ensures sint(A) == (sint(x) * sint(y) * power(BASE_INV, n)) % sint(m);
    {
        A  := zero_seq_int(n + 1);
        assert sint(A) == 0;

        ghost var m_val := sint(m);
        ghost var y_val := sint(y);

        var i := 0;

        assert cong(sint(A), sint(x[..i]) * y_val * power(BASE_INV, i), m_val) by {
            calc ==> {
                m_val != 0;
                {
                    reveal cong();
                }
                cong(0, 0, m_val);
                {
                    assert sint(A) == 0;
                }
                cong(sint(A), 0, m_val);
                {
                    assert sint(x[..i]) == 0;
                    assert sint(x[..i]) * y_val * power(BASE_INV, i) == 0;
                }
                cong(sint(A), sint(x[..i]) * y_val * power(BASE_INV, i), m_val);
            }
        }
        
        while i < n
            decreases n - i;
            invariant |A| == n + 1;
            invariant i <= |x|;
            invariant cong(sint(A), sint(x[..i]) * sint(y) * power(BASE_INV, i), sint(m));
            invariant sint(A) < 2 * m_val - 1;
            invariant cong(BASE * BASE_INV, 1, sint(m));
        {
            var u_i_ := ((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE; 
            var u_i := u_i_ as uint32;

            var P_1 := magic_mul(y, x[i], n);
            var P_2 := magic_mul(m, u_i, n);
            var S := seq_add_c(P_1, P_2, n + 1);
    
            A := seq_zero_extend(A, n + 1, n + 2);
            var A' := seq_add_c(A, S, n + 2);

            assert sint(A') % BASE == 0 && cong(A'[0] as int, 0, BASE) by {
                mont_mul_divisible_lemma(m, x, y, P_1, P_2, S, A, A', i, u_i, m', n);
            }

            var A'' := A'[1..n+2];

            assert (sint(A'') == sint(A') / BASE) && sint(A'') < 2 * m_val - 1 by {
                mont_mul_bounded_lemma(m, x, y, P_1, P_2, S, A, A', A'', i, u_i, m', n);
            }

            assert cong(sint(A''), sint(x[..i + 1]) * y_val * power(BASE_INV, i+1), m_val) by {
                mont_mul_congruent_lemma(m, x, y, P_1, P_2, S, A, A', A'', i, u_i, m', n, BASE_INV);
            }

            i := i + 1;
            A := A'';
        }

        assert x[..n] == x;

        assert sint(A) < 2 * m_val - 1;
        assert cong(sint(A), sint(x) * sint(y) * power(BASE_INV, n), sint(m));

        var m_ext := seq_zero_extend(m, n, n + 1);
        var geq := seq_geq(A, m_ext);

        if geq {
            var b, D := seq_sub(A, m_ext);

            assert cong(sint(A), sint(A) - m_val, m_val) by {
                cong_add_lemma_3(sint(A), - (m_val as int), m_val);
            }

            calc ==> {
                cong(sint(A), sint(A) - m_val, m_val);
                {
                   reveal cong(); 
                }
                cong(sint(A) - m_val, sint(A), m_val);
                {
                    assert cong(sint(A), sint(x) * sint(y) * power(BASE_INV, n), sint(m));
                    cong_trans_lemma(sint(A) - m_val, sint(A), sint(x) * sint(y) * power(BASE_INV, n), sint(m));
                }
                cong(sint(A) - m_val, sint(x) * sint(y) * power(BASE_INV, n), sint(m));
                {
                    assert sint(D) == sint(A) - m_val;
                }
                cong(sint(D), sint(x) * sint(y) * power(BASE_INV, n), sint(m));
            }
            A := D;
        }

        ghost var temp := sint(x) * sint(y) * power(BASE_INV, n);

        assert sint(A) == temp % sint(m) by {
            assert cong(temp, sint(A), sint(m)) by {
                assert cong(sint(A), temp, sint(m));
                reveal cong();
            }
            assert sint(A) < m_val;
            cong_residual_lemma(temp, sint(A), sint(m));
        }
    }

    lemma mont_mul_divisible_lemma(m: seq<uint32>,
        x: seq<uint32>,
        y: seq<uint32>,
        P_1: seq<uint32>,
        P_2: seq<uint32>,
        S: seq<uint32>,
        A: seq<uint32>,
        A': seq<uint32>,
        i: nat,
        u_i: uint32,
        m': uint32,
        n: nat)

        requires n > 2 && i < n;
        requires |m| == |x| == |y| == n;
        requires |P_1| ==|P_2| == n + 1;
        requires |S| == |A| == n + 2;
        requires |A'| == n + 3;
        requires cong(m' as int * sint(m), -1, BASE);

        requires u_i as int == ((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE;

        requires cong(P_1[0] as int, y[0] as int * x[i] as int, BASE);
        requires cong(P_2[0] as int, m[0] as int * u_i as int, BASE);
        requires cong(A'[0] as int, A[0] as int + S[0] as int, BASE);

        requires sint(A) + sint(S) == sint(A');

        requires cong(S[0] as int, P_1[0] as int + P_2[0] as int, BASE);

        ensures cong(A'[0] as int, 0, BASE);
        ensures sint(A') % BASE == 0;
    {
        assert cong(m' as int * m[0] as int, -1, BASE) by {
                lsw_inverse_lemma(m, m');
        }

        calc ==> {
            cong(S[0] as int, P_1[0] as int + P_2[0] as int, BASE);
            {
                cong_add_lemma_1(S[0] as int, P_1[0] as int + P_2[0] as int, A[0] as int,BASE);
            }
            cong(S[0] as int + A[0] as int, P_1[0] as int + P_2[0] as int + A[0] as int, BASE);
            {
                cong_trans_lemma(A'[0] as int, A[0] as int + S[0] as int,
                    P_1[0] as int + P_2[0] as int + A[0] as int,
                    BASE);
            }
            cong(A'[0] as int, P_1[0] as int + P_2[0] as int + A[0] as int, BASE);
            {
                assert cong(P_1[0] as int + P_2[0] as int + A[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int + A[0] as int, BASE) by {
                    assert cong(P_1[0] as int + P_2[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int, BASE) by {
                        assert cong(P_1[0] as int, y[0] as int * x[i] as int, BASE);
                        assert cong(P_2[0] as int, m[0] as int * u_i as int, BASE);
                        cong_add_lemma_2(P_1[0] as int, y[0] as int * x[i] as int, P_2[0] as int, m[0] as int * u_i as int, BASE);
                    }
                    cong_add_lemma_1(P_1[0] as int + P_2[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int, A[0] as int, BASE);
                }
                cong_trans_lemma(A'[0] as int, P_1[0] as int + P_2[0] as int + A[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int + A[0] as int, BASE);
            }
            cong(A'[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int + A[0] as int, BASE);
            {
                assert u_i as int == ((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE;
            }
            cong(A'[0] as int, y[0] as int * x[i] as int + m[0] as int * (((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE) + A[0] as int, BASE);
            {
                assert cong(y[0] as int * x[i] as int + m[0] as int * (((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE) + A[0] as int, 0, BASE) by {
                    mont_mul_div_aux_lemma_1(y[0] as int, x[i] as int, m[0] as int, A[0] as int , m' as int);
                }
                cong_trans_lemma(A'[0] as int, y[0] as int * x[i] as int + m[0] as int * (((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE) + A[0] as int, 0, BASE);
            }
            cong(A'[0] as int, 0, BASE);
        }
        assert cong(A'[0] as int, 0, BASE);

        assert sint(A') % BASE == 0 by {
            seq_div_base_lemma(A', n + 3);
        }
    }

    lemma mont_mul_div_aux_lemma_1(y: int, x: int, m: int, a: int, m': int)
        requires cong(m' * m, -1, BASE);
        ensures cong(y * x + m * (((a + x * y) * m') % BASE) + a, 0, BASE);
    {
        ghost var temp_1 := m * (((a + x * y) * m') % BASE);
        ghost var temp_2 := -(a + x * y);
        ghost var temp_3 := x * y;

        assert cong(temp_1, temp_2, BASE) by {
            mont_mul_div_aux_lemma_2(y, x, m, a, m');
        }

        calc ==> {
            cong(temp_1, temp_2, BASE);
            {
                cong_add_lemma_1(temp_1, temp_2, temp_3, BASE);
            }
            cong(temp_1 + temp_3, temp_2 + temp_3, BASE);
            cong(temp_1 + temp_3, -(a + x * y) + x * y, BASE);
            cong(temp_1 + temp_3, -a - x * y + x * y, BASE);
            cong(temp_1 + temp_3, -a, BASE);
            {
                cong_add_lemma_1(temp_1 + temp_3, -a, a, BASE);
            }
            cong(temp_1 + temp_3 + a, 0, BASE);
            cong(temp_3 + temp_1 + a, 0, BASE);
            cong(x * y + temp_1 + a, 0, BASE);
            cong(x * y + m * (((a + x * y) * m') % BASE) + a, 0, BASE);
        }
        assert cong(x * y + m * (((a + x * y) * m') % BASE) + a, 0, BASE);
    }

    lemma mont_mul_div_aux_lemma_2(y: int, x: int, m: int, a: int, m': int)
        requires cong(m' * m, -1, BASE);
        ensures cong(m * (((a + x * y) * m') % BASE), -(a + x * y), BASE);
    {
        assert A_1: cong(((a + x * y) * m') % BASE, (a + x * y) * m', BASE) by {
            cong_mod_lemma((a + x * y) * m', BASE);
        }

        ghost var temp_1 := m * (((a + x * y) * m') % BASE);
        ghost var temp_2 := -(a + x * y);
   
        calc ==> {
            cong(((a + x * y) * m') % BASE, (a + x * y) * m', BASE);
            {
                cong_mul_lemma_1(((a + x * y) * m') % BASE, (a + x * y) * m', m, BASE);
            }
            cong(temp_1, m * (a + x * y) * m', BASE);
            {
                assert m * (a + x * y) * m' == m * m' * (a + x * y);
            }
            cong(temp_1, m * m' * (a + x * y), BASE);
            {
                assert cong(m * m' * (a + x * y), -(a + x * y), BASE) by {
                    assert cong(m' * m, -1, BASE);
                    cong_mul_lemma_1(m' * m, -1, (a + x * y), BASE);
                }
                cong_trans_lemma(temp_1, m * m' * (a + x * y), -(a + x * y), BASE);
            }
            cong(temp_1, -(a + x * y), BASE);
            cong(temp_1, temp_2, BASE);
        }

        assert cong(temp_1, temp_2, BASE) by {
            reveal A_1;
        }

        calc ==> {
            cong(temp_1, temp_2, BASE);
            cong(m * (((a + x * y) * m') % BASE), temp_2, BASE);
            cong(m * (((a + x * y) * m') % BASE), -(a + x * y), BASE);
        }

        assert cong(m * (((a + x * y) * m') % BASE), -(a + x * y), BASE);
    }

    lemma mont_mul_bounded_lemma(
        m: seq<uint32>,
        x: seq<uint32>,
        y: seq<uint32>,
        P_1: seq<uint32>,
        P_2: seq<uint32>,
        S: seq<uint32>,
        A: seq<uint32>,
        A': seq<uint32>,
        A'': seq<uint32>,
        i: nat,
        u_i: uint32,
        m': uint32,
        n: nat)

        requires i < n;
        requires |m| == n && |x| == n && |y| == n;
        requires |A| == n + 2;
        requires |A'| == n + 3;

        requires A'' == A'[1..n+2];

        requires sint(A) < 2 * sint(m) - 1;
        requires sint(A) + sint(S) == sint(A');
        requires sint(P_1) + sint(P_2) == sint(S);
        requires sint(P_1) == sint(y) * x [i] as int;
        requires sint(P_2) == sint(m) * u_i as int;

        requires 0 <= sint(x) < sint(m);
        requires 0 <= sint(y) < sint(m);

        requires cong(A'[0] as int, 0, BASE);

        ensures sint(A'') < 2 * sint(m) - 1;
        ensures sint(A'') == sint(A') / BASE;
    {
        ghost var m_val := sint(m);
        ghost var m_bound := m_val - 1;
        ghost var base_bound := BASE - 1;

        calc <= {
            sint(A');
            sint(A) + sint(S);
            sint(A) + sint(P_1) + sint(P_2);
            sint(A) + sint(y) * x [i] as int + sint(P_2);
            {
                assert sint(y) <= m_bound;
            }
            sint(A) + m_bound * x [i] as int + sint(P_2);
            {
                assert x [i] as int <= base_bound;
            }
            sint(A) + m_bound * base_bound + sint(P_2);
            sint(A) + m_bound * base_bound + sint(m) * u_i as int;
            {
                assert u_i as int <= base_bound;
            }
            sint(A) + m_bound * base_bound + sint(m) * base_bound;
            sint(A) + m_bound * base_bound + m_val * base_bound;
        }

        calc ==> {
            sint(A') < 2 * m_val - 1 + m_bound * base_bound + m_val * base_bound;
            sint(A') < 2 * m_val - 1 + (m_val - 1) * base_bound + m_val * base_bound;
            sint(A') < 2 * m_val - 1 + m_val * base_bound - base_bound + m_val * base_bound;
            sint(A') < 2 * m_val - 1 + m_val * (BASE - 1) - (BASE - 1) + m_val * (BASE - 1);
            sint(A') < 2 * m_val + m_val * (BASE - 1) - BASE + m_val * (BASE - 1);
            sint(A') < 2 * m_val + m_val * BASE - m_val - BASE + m_val * (BASE - 1);
            sint(A') < 2 * m_val + m_val * BASE - m_val - BASE + m_val * BASE - m_val;
            sint(A') < m_val * BASE - BASE + m_val * BASE;
            sint(A') < 2 * m_val * BASE - BASE;
            sint(A') < BASE * (2 * m_val - 1);
            sint(A') < BASE * (2 * sint(m) - 1);
        }

        var T_1 := A'[1..];
    
        assert sint(T_1) == sint(A') / BASE by {
            seq_div_base_lemma(A', n + 3);
        }
        assert sint(T_1) < 2 * sint(m) - 1;

        var T_2 := T_1[..n+1];
        assert T_2 == A'[1..n+2];

        assert sint(T_2) == sint(T_1) by {
            assert sint(T_1) < 2 * R(n) - 1 by {
                sint_upper_bound_lemma(m, n);
            }
            msw_zero_lemma(T_1, n);
            zero_extend_lemma(T_2, n + 1, T_1, n + 2);
        }

        assert sint(A'[1..n+2]) < 2 * sint(m) - 1;
        assert sint(A'') == sint(A') / BASE;
    }

    lemma mont_mul_congruent_aux_lemma_1(
        x: seq<uint32>,
        i: nat,
        y_val: int,
        p: int,
        p_inv: int,
        BASE_INV: int,
        m_val: int)

        requires m_val != 0;
        requires i + 1 <= |x|;
        requires cong(BASE * BASE_INV, 1, m_val);
        requires p == power(BASE, i);
        requires p_inv == power(BASE_INV, i);
        
        ensures (y_val * (sint(x[..i]) * p_inv + x[i] as int)) % m_val == (y_val * sint(x[..i+1]) * p_inv) % m_val;
    {
        ghost var x_1 := x[..i];
        ghost var x_2 := x[..i+1];

        calc ==> {
            cong(BASE * BASE_INV, 1, m_val);
            {
                cong_power_lemma(BASE * BASE_INV, 1, i, m_val);
            }
            cong(power(BASE * BASE_INV, i), power(1, i), m_val);
            {
                power_base_one_lemma(i);
            }
            cong(power(BASE * BASE_INV, i), 1, m_val);
            {
                power_same_exp_lemma(BASE, BASE_INV, i);
            }
            cong(power(BASE, i) * power(BASE_INV, i), 1, m_val);
            cong(p * p_inv, 1, m_val);
        }

        assert cong(p * p_inv, 1, m_val);

        assert cong(1, p * p_inv, m_val) by {
            reveal cong();
        }

        calc == {
            (sint(x_1) * p_inv + x[i] as int) % m_val;
            {
                ghost var a := sint(x_1) * p_inv + x[i] as int;
                assert a % m_val == a * p * p_inv % m_val by {
                    cong_mul_lemma_1(1, p * p_inv, a, m_val);
                    reveal cong();
                }
            }
            ((sint(x_1) * p_inv + x[i] as int) * p * p_inv) % m_val;
            {
                assert (sint(x_1) * p_inv + x[i] as int) * p == (sint(x_1) * p_inv * p  + x[i] as int * p);
            }
            ((sint(x_1) * p_inv * p + x[i] as int * p) * p_inv) % m_val;
            {
                mont_mul_congruent_aux_lemma_2(x, i, x_1, x_2, p, p_inv, BASE_INV, m_val);
            }
            (sint(x_2) * p_inv) % m_val;
        }
        
        ghost var a := sint(x_1) * p_inv + x[i] as int;
        ghost var b := sint(x_2) * p_inv;

        assert a % m_val == b % m_val by {
            assert (sint(x_1) * p_inv + x[i] as int) % m_val == (sint(x_2) * p_inv) % m_val;
        }

        calc ==> {
            a % m_val == b % m_val;
            {
                reveal cong();
            }
            cong(a, b, m_val);
            {
                cong_mul_lemma_1(a, b, y_val, m_val);
            }
            cong(y_val * a, y_val * b, m_val);
            {
                reveal cong();
            }
            (y_val * a) % m_val == (y_val * b) % m_val;
            (y_val * (sint(x_1) * p_inv + x[i] as int)) % m_val == (y_val * (sint(x_2) * p_inv)) % m_val;
            {
                assert y_val * (sint(x_2) * p_inv) == y_val * sint(x_2) * p_inv;
            }
            (y_val * (sint(x_1) * p_inv + x[i] as int)) % m_val == (y_val * sint(x_2) * p_inv) % m_val;
        }

        assert (y_val * (sint(x_1) * p_inv + x[i] as int)) % m_val == (y_val * sint(x_2) * p_inv) % m_val;
    }

    lemma mont_mul_congruent_aux_lemma_2(
        x: seq<uint32>,
        i: nat,
        x_1: seq<uint32>,
        x_2: seq<uint32>,
        p: int,
        p_inv: int,
        BASE_INV: int,
        m_val: int)

        requires i + 1 <= |x|;
        requires x_1 == x[..i] && x_2 == x[..i+1];
        requires p == power(BASE, i);
        requires p_inv == power(BASE_INV, i);
        requires m_val != 0;
        requires cong(p * p_inv, 1, m_val);

        ensures ((sint(x_1) * p_inv * p + x[i] as int * p) * p_inv) % m_val == (sint(x_2) * p_inv) % m_val;
    {
        ghost var a := sint(x_1);
        ghost var b := x[i] as int * p;

        assert assertion_1 : (sint(x_1) * p_inv * p + x[i] as int * p) * p_inv % m_val == (sint(x_1) + x[i] as int * p) * p_inv % m_val by {
            calc ==> {
                cong(p * p_inv, 1, m_val);
                {
                    cong_mul_lemma_1(p * p_inv, 1, sint(x_1), m_val);
                }
                cong(a * p * p_inv, a, m_val);
                { 
                    cong_add_lemma_1(a * p * p_inv, a, b, m_val);
                }
                cong(a * p * p_inv + b, a + b, m_val);
                {
                    cong_mul_lemma_1(a * p * p_inv + b, a + b, p_inv, m_val);
                }
                cong((a * p * p_inv + b) * p_inv, (a + b) * p_inv, m_val);
                {
                    reveal cong();    
                }
                ((a * p * p_inv + b) * p_inv) % m_val == (a + b) * p_inv % m_val;
            }
            assert ((a * p * p_inv + b) * p_inv) % m_val == (a + b) * p_inv % m_val;
        }

        calc == {
            sint(x_2);
            interp(x_2, i + 1);
            x_2[i] as int * p + interp(x_2, i);
            {
                prefix_sum_lemma(x_1, x_2, i);
                assert interp(x_1, i) == interp(x_2, i);
                assert sint(x_1) == interp(x_2, i);
            }
            x_2[i] as int * p + sint(x_1);
        }

        assert ((sint(x_1) * p_inv * p + x[i] as int * p) * p_inv) % m_val == (sint(x_2) * p_inv) % m_val by {
            reveal assertion_1;
            assert sint(x_2) == x_2[i] as int * p + sint(x_1);
        }
    }

    lemma mont_mul_congruent_lemma(
        m: seq<uint32>,
        x: seq<uint32>,
        y: seq<uint32>,
        P_1: seq<uint32>,
        P_2: seq<uint32>,
        S: seq<uint32>,
        A: seq<uint32>,
        A': seq<uint32>,
        A'': seq<uint32>,
        i: nat,
        u_i: uint32,
        m': uint32,
        n: nat,
        BASE_INV: nat)

        requires i < n;
        requires |m| == n && |x| == n && |y| == n;
        requires |A| == n + 2;
        requires |A'| == n + 3;

        requires A'' == A'[1..n+2];
        requires sint(A'') == sint(A') / BASE;
        requires sint(A') % BASE == 0;

        requires sint(m) != 0;
        requires sint(A) + sint(S) == sint(A');
        requires sint(P_1) + sint(P_2) == sint(S);
        requires sint(P_1) == sint(y) * x [i] as int;
        requires sint(P_2) == sint(m) * u_i as int;

        requires cong(BASE * BASE_INV, 1, sint(m));

        requires cong(sint(A), sint(x[..i]) * sint(y) * power(BASE_INV, i), sint(m));
        ensures cong(sint(A''), sint(x[..i + 1]) * sint(y) * power(BASE_INV, i+1), sint(m));
    {
        ghost var m_val := sint(m);
        ghost var y_val := sint(y);
        ghost var p := power(BASE, i);
        ghost var p_inv := power(BASE_INV, i);

        ghost var x_1 := x[..i];
        ghost var x_2 := x[..i+1];

        ghost var A_val' := sint(A');

        calc == {
            sint(A') % m_val;
            (sint(A) + sint(S)) % m_val;
            (sint(A) + sint(P_1) + sint(P_2)) % m_val;
            {
                calc ==> {
                    sint(P_2) == sint(m) * u_i as int;
                    {
                        mod_mul_lemma(u_i as int, sint(m), m_val);
                    }
                    sint(P_2) % m_val == 0;
                    {
                         cong_add_lemma_3(sint(A) + sint(P_1), sint(P_2), m_val);
                     }
                    cong(sint(A) + sint(P_1), sint(A) + sint(P_1) + sint(P_2), m_val);
                }
                reveal cong();
            }
            (sint(A) + sint(P_1)) % m_val;
            {
                assert cong(sint(A), sint(x_1) * y_val * p_inv, m_val);
                cong_add_lemma_1(sint(A), sint(x_1) * y_val * p_inv, sint(P_1), m_val);
                reveal cong();
            }
            (sint(x_1) * y_val * p_inv + sint(P_1)) % m_val;
            {
                assert sint(P_1) == sint(y) * x [i] as int;
            }
            (sint(x_1) * y_val * p_inv + y_val * x[i] as int) % m_val;
            {
                assert sint(x_1) * y_val * p_inv == y_val * sint(x_1) * p_inv by {
                    assert sint(x_1) * y_val == y_val * sint(x_1);
                }
            }
            (y_val * sint(x_1) * p_inv + y_val * x[i] as int) % m_val;
            {
                assert y_val * sint(x_1) * p_inv + y_val * x[i] as int == y_val * (sint(x_1) * p_inv + x[i] as int);
            }
            (y_val * (sint(x_1) * p_inv + x[i] as int)) % m_val;
            {
                mont_mul_congruent_aux_lemma_1(x, i, y_val, p, p_inv, BASE_INV, m_val);
            }
            (y_val * sint(x_2) * p_inv) % m_val;
        }

        assert assertion_1: cong(sint(A'), y_val * sint(x_2) * p_inv, m_val) by {
            reveal cong();
        }

        calc == {
            sint(A'') % m_val;
            {
                assert sint(A'') == sint(A') / BASE;
            }
            (sint(A') / BASE) % m_val;
            {
                mod_div_inv_leamma(sint(A'), BASE, BASE_INV, m_val);
                reveal cong();
            }
            (sint(A') * BASE_INV) % m_val;
            {
                reveal assertion_1;
                calc ==> {
                    cong(sint(A'), y_val * sint(x_2) * p_inv, m_val);
                    {
                        cong_mul_lemma_1(sint(A'), y_val * sint(x_2) * p_inv, BASE_INV, m_val);
                    }
                    cong(sint(A') * BASE_INV, y_val * sint(x_2) * p_inv * BASE_INV, m_val);
                    {
                        reveal cong();
                    }
                    (sint(A') * BASE_INV) % m_val == (y_val * sint(x_2) * p_inv * BASE_INV) % m_val;
                }
            }
            (y_val * sint(x_2) * p_inv * BASE_INV) % m_val;
            {
                ghost var a := y_val * sint(x_2);
                assert a * p_inv * BASE_INV == a * power(BASE_INV, i+1) by {
                    calc == {
                        p_inv * BASE_INV;
                        power(BASE_INV, i) * BASE_INV;
                        {
                            power_add_one_lemma(BASE_INV, i);
                        }
                        power(BASE_INV, i+1);
                    }
                    assert p_inv * BASE_INV == power(BASE_INV, i+1);
                }
            }
            (y_val * sint(x_2) * power(BASE_INV, i+1)) % m_val;
        }
        
        assert cong(sint(A''), y_val * sint(x_2) * power(BASE_INV, i+1), sint(m)) by {
            assert sint(A'') % m_val == (y_val * sint(x_2)* power(BASE_INV, i+1)) % m_val;
            reveal cong();
        }
    }

    method magic_mul(A: seq<uint32>, b: uint32, n: nat)
        returns (P: seq<uint32>)
        requires n != 0;
        requires |A| == n;
        ensures |P| == n + 1;
        ensures sint(P) == sint(A) * b as int;
        ensures cong(P[0] as int, A[0] as int * b as int, BASE);
    {
        var temp := new uint32[n + 1];
        temp[0] := 0;
        P := temp[..];

        assert P[0] == 0;

        var i := 0;
        var c :uint32 := 0;

        while i < n 
            decreases n - i;
            invariant |A| == n;
            invariant |P| == n + 1;
            invariant i < |P|;
            invariant sint(P[..i]) + c as int * power(BASE, i) == sint(A[..i]) * b as int;
            invariant i >= 1 ==> P[0] as int == (A[0] as int * b as int) % BASE;
        {
            single_digit_mul_lemma(A[i], b, c);
            var product :uint64 := A[i] as uint64 * b as uint64 + c as uint64;

            var lower, upper := split64(product);

            assert lower as int + upper as int  * BASE == product as int;

            P := P[i := lower];

            if i == 0 {
                assert P[0] as int == (A[0] as int * b as int) % BASE;
            }

            i := i + 1;

            calc == {
                sint(P[..i]) + upper as int * power(BASE, i);
                word_interp(P[..i], i - 1) + interp(P[..i], i - 1) + upper as int * power(BASE, i) ;
                {
                    prefix_sum_lemma(P[..i], P[..i - 1], i - 1);
                }
                word_interp(P[..i], i - 1) + interp(P[..i - 1], i - 1) + upper as int * power(BASE, i) ;
                lower as int * power(BASE, i - 1) + interp(P[..i - 1], i - 1) + upper as int * power(BASE, i);
                {
                    calc == {
                        lower as int * power(BASE, i - 1) + upper as int * power(BASE, i);
                        {
                            power_add_one_lemma(BASE, i - 1);
                            assert power(BASE, i) == power(BASE, i - 1) * BASE;
                        }
                        lower as int * power(BASE, i - 1) + upper as int * power(BASE, i - 1) * BASE;
                        power(BASE, i - 1) * (lower as int  + upper as int * BASE);
                    }

                    assert lower as int  * power(BASE, i - 1) + upper as int * power(BASE, i) == power(BASE, i - 1) * (lower as int + upper as int  * BASE);
                }
                power(BASE, i - 1) * (lower as int + upper as int  * BASE) + interp(P[..i - 1], i - 1);
                power(BASE, i - 1) * product as int + interp(P[..i - 1], i - 1);
                power(BASE, i - 1) * (A[i - 1]  as int * b  as int + c as int) + interp(P[..i - 1], i - 1);
                {
                    assert sint(P[..i - 1]) + c as int * power(BASE, i - 1) == sint(A[..i -1]) * b as int;
                    assert sint(P[..i - 1]) == sint(A[..i -1]) * b as int - c as int * power(BASE, i - 1);
                }
                power(BASE, i - 1) * (A[i - 1]  as int * b  as int + c as int) + sint(A[..i -1]) * b as int - c as int * power(BASE, i - 1);
                power(BASE, i - 1) * A[i - 1] as int * b  as int + sint(A[..i -1]) * b as int;
                (power(BASE, i - 1) * A[i - 1] as int + sint(A[..i -1])) * b as int;
                (word_interp(A, i - 1) + interp(A[..i-1], i - 1)) * b as int;
                {
                    prefix_sum_lemma(A[..i-1], A[..i], i - 1);
                }
                (word_interp(A, i - 1) + interp(A[..i], i - 1)) * b as int;
                sint(A[..i]) * b as int;
            }

            c := upper;
        }
    
        P := P[n := c];
        
        calc ==> {
            sint(P[..i]) + c as int * power(BASE, i) == sint(A[..i]) * b as int;
            {
                prefix_sum_lemma(A, A[..i], i);
            }
            sint(P[..i]) + c as int * power(BASE, i) == sint(A) * b as int;
            {
                assert sint(P[..i]) == interp(P[..i], i);
                prefix_sum_lemma(P, P[..i], i);
            }
            interp(P, i) + c as int * power(BASE, i) == sint(A) * b as int;
            interp(P, i) + word_interp(P, i) == sint(A) * b as int;
            interp(P, i + 1) == sint(A) * b as int;
            sint(P) == sint(A) * b as int;
        }

        assert cong(P[0] as int, A[0] as int * b as int, BASE) by {
            assert P[0] as int == (A[0] as int * b as int) % BASE;
            reveal cong();
        }
    }

    lemma single_digit_mul_lemma(a: uint32, b: uint32, c: uint32)
        ensures a as nat * b as nat + c as nat < UINT64_MAX as int;
    {
        assert a as nat * b as nat <= 0xfffffffe00000001 by {
            single_digit_mul_aux_lemma_1(a, b);
        }
        assert a as nat * b as nat + c as nat <= 0xffffffff00000000;
    }

    lemma single_digit_mul_aux_lemma_1(a: uint32, b: uint32)
        ensures a as nat * b as nat <= 0xfffffffe00000001;
    {
        var u : nat := 0xffffffff;
        calc ==> {
            a as nat <= u && b as nat <= u;
            {
                single_digit_mul_aux_lemma_2(a as nat, b as nat, u);
            }
            a as nat * b as nat <= u * u;
            {
                assert u * u == 0xfffffffe00000001;
            }
            a as int * b as int <= 0xfffffffe00000001;
        }
    }

    lemma single_digit_mul_aux_lemma_2(a:nat, b:nat, u:nat)
        requires a <= u;
        requires b <= u;
        ensures a * b <= u * u;
    {
        assert true;
    }
}