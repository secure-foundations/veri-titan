include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"
include "SeqInt.dfy"
include "RSAE3v1.dfy"
include "RSALemmas.dfy"

module MMLemmas {
    import opened NativeTypes
    import opened Powers
    import opened Congruences
    import opened SeqInt
    import opened RSALemmas
    import opened RSAE3v1

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

    lemma cmm_divisible_lemma_1(p_1: nat, p_2: nat, x_i: nat, y_0: nat, a_0: nat, u_i: nat, m': nat, m_0: nat)
        requires cong(m' * m_0, -1, BASE);
        requires p_1 <= UINT64_MAX as nat;
        requires p_1 == x_i * y_0 + a_0;
        requires u_i == (lh64(p_1 as uint64) as nat * m') % BASE;
        requires p_2 == u_i * m_0 + lh64(p_1 as uint64) as nat;
        ensures cong(p_2, 0, BASE);
    {
        assert lh64(p_1 as uint64) as nat == p_1 % BASE by {
            split64_lemma(p_1 as uint64);
        }

        calc ==> {
            cong(m' * m_0, -1, BASE);
            {
                mont_mul_div_aux_lemma_1(y_0, x_i, m_0, a_0, m');
            }
            cong(y_0 * x_i + a_0 + m_0 * (((a_0 + x_i * y_0) * m') % BASE) , 0, BASE);
            {
                assert p_1 == x_i * y_0 + a_0;
            }
            cong(p_1 + m_0 * ((p_1 * m') % BASE) , 0, BASE);
            {
                cong_mod_lemma(p_1, BASE);
                assert cong(p_1 % BASE, p_1, BASE);
                cong_mul_lemma_1(p_1 % BASE, p_1, m', BASE);
                assert cong((p_1 % BASE) * m', p_1 * m', BASE);
                reveal cong();
                assert (p_1 % BASE * m') % BASE == (p_1 * m') % BASE;
                assert u_i == (p_1 * m') % BASE;
            }
            cong(p_1 + m_0 * u_i , 0, BASE);
            {
                cong_mod_lemma(p_1, BASE);
                assert cong(p_1 % BASE, p_1, BASE);
                cong_add_lemma_1(p_1 % BASE, p_1,  m_0 * u_i, BASE); 
                assert cong(p_1 % BASE + m_0 * u_i, p_1 + m_0 * u_i, BASE);
                cong_trans_lemma(p_1 % BASE + m_0 * u_i, p_1 + m_0 * u_i, 0, BASE);
            }
            cong(p_1 % BASE + m_0 * u_i , 0, BASE);
            cong(p_2, 0, BASE);
        }
    }

    lemma cmm_invarint_lemma_1(
        m: seq<uint32>,
        A: seq<uint32>, 
        x_i: uint32,
        y: seq<uint32>,
        n: nat,
        p_1: uint64,
        p_2: uint64,
        u_i: uint32)

        requires |m| == |A| == |y| == n >= 1;
        requires p_1 as int == x_i as int * y[0] as int  + A[0] as int;
        requires p_2 as int == u_i as int * m[0] as int + lh64(p_1) as int;
        requires cong(p_2 as int, 0, BASE);

        ensures x_i as nat * sint(y[..1]) + u_i as nat * sint(m[..1]) + sint(A[..1]) as nat == 
            uh64(p_2) as int * power(BASE, 1) + uh64(p_1) as int * power(BASE, 1);
    {
        calc == {
            x_i as nat * sint(y[..1]) + u_i as nat * sint(m[..1]) + sint(A[..1]);
            {
                assert power(BASE, 0) == 1 by {
                    reveal power();
                }
            }
            x_i as nat * y[0] as nat + u_i as nat * m[0] as nat + A[0] as nat;
            u_i as nat * m[0] as nat + p_1 as int;
            {
                split64_lemma(p_1);
            }
            u_i as nat * m[0] as nat + lh64(p_1) as int + uh64(p_1) as int * BASE;
            p_2 as int + uh64(p_1) as int * BASE;
            {
                split64_lemma(p_2);
            }
            lh64(p_2) as int + uh64(p_2) as int * BASE + uh64(p_1) as int * BASE;
            {
                assert p_2 as int % BASE == 0 by {
                    assert cong(p_2 as int, 0, BASE);
                    reveal cong();
                }
                split64_lemma(p_2);
                assert lh64(p_2) == 0;
            }
            uh64(p_2) as int * BASE + uh64(p_1) as int * BASE;
            {
                reveal power();
            }
            uh64(p_2) as int * power(BASE, 1) + uh64(p_1) as int * power(BASE, 1);
        }
    }

    lemma cmm_invarint_lemma_2(
        m: seq<uint32>,
        A: seq<uint32>, 
        x_i: uint32,
        y: seq<uint32>,
        n: nat,
        p_1: uint64,
        p_1': uint64,
        p_2: uint64,
        p_2': uint64,
        u_i: uint32,
        j: nat,
        S: seq<uint32>,
        S': seq<uint32>)
    
        requires |m| == |A| == |y| == n;
        requires 0 < j <= n;
        requires |S| == j;
        requires S == S' + [lh64(p_2)];

        requires x_i as nat * sint(y[..j-1]) + u_i as nat * sint(m[..j-1]) + sint(A[..j-1]) == 
                sint(S') + uh64(p_2') as int * power(BASE, j-1) + uh64(p_1') as int * power(BASE, j-1);
        requires p_1 as nat == uh64(p_1') as nat + x_i as nat * y[j-1] as nat + A[j-1] as nat;
        requires p_2 as nat == uh64(p_2') as nat + u_i as nat * m[j-1] as nat + lh64(p_1) as nat;

        ensures u_i as nat * sint(m[..j]) + x_i as nat * sint(y[..j]) + sint(A[..j]) == 
            sint(S) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
    {
        calc == {
            sint(S) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
            lh64(p_2) as nat * power(BASE, j-1) + interp(S, j-1) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
            {
                prefix_sum_lemma(S, S', j-1);
            }
            lh64(p_2) as nat * power(BASE, j-1) + sint(S') + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
            {
                power_add_one_lemma(BASE, j - 1);
                assert uh64(p_2) as int * power(BASE, j) == uh64(p_2) as int * BASE * power(BASE, j - 1);
            }
            lh64(p_2) as nat * power(BASE, j-1) + sint(S') + uh64(p_2) as int * BASE * power(BASE, j - 1) + uh64(p_1) as int * power(BASE, j);
            lh64(p_2) as nat * power(BASE, j-1) + uh64(p_2) as int * BASE * power(BASE, j - 1 ) + sint(S') + uh64(p_1) as int * power(BASE, j);
            {
                assert lh64(p_2) as nat * power(BASE, j-1) + uh64(p_2) as int * BASE * power(BASE, j - 1) == 
                    (lh64(p_2) as nat + uh64(p_2) as int * BASE) * power(BASE, j - 1);
            }
            (lh64(p_2) as int  + uh64(p_2) as int * BASE) * power(BASE, j-1) + sint(S') + uh64(p_1) as int * power(BASE, j);
            {
                split64_lemma(p_2);
            }
            p_2 as int * power(BASE, j-1) + sint(S') + uh64(p_1) as int * power(BASE, j);
            {
                assert p_2 as nat == uh64(p_2') as nat + u_i as nat * m[j-1] as nat + lh64(p_1) as nat;
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat + lh64(p_1) as nat) * power(BASE, j-1) + sint(S') + uh64(p_1) as int * power(BASE, j);
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + lh64(p_1) as nat * power(BASE, j-1) + sint(S') + uh64(p_1) as int * power(BASE, j);
            {
                power_add_one_lemma(BASE, j - 1);
                assert uh64(p_1) as int * power(BASE, j) == uh64(p_1) as int * BASE * power(BASE, j - 1);
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + lh64(p_1) as nat * power(BASE, j-1) + sint(S') +  uh64(p_1) as int * BASE * power(BASE, j - 1);
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + sint(S') + lh64(p_1) as nat * power(BASE, j-1) +  uh64(p_1) as int * BASE * power(BASE, j - 1);
            {
                assert lh64(p_1) as nat * power(BASE, j-1) +  uh64(p_1) as int * BASE * power(BASE, j - 1) == (lh64(p_1) as nat +  uh64(p_1) as int * BASE) * power(BASE, j - 1);
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + sint(S')  + (lh64(p_1) as nat + uh64(p_1) as nat * BASE)* power(BASE, j-1);
            {
                split64_lemma(p_1);
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + sint(S')  + p_1 as nat * power(BASE, j-1);
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + uh64(p_2') as nat * power(BASE, j-1) + sint(S')  + p_1 as nat * power(BASE, j-1);
            {
                assert p_1 as nat == uh64(p_1') as nat + x_i as nat * y[j-1] as nat + A[j-1] as nat;
            }
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + uh64(p_2') as nat * power(BASE, j-1) + sint(S')  + (uh64(p_1') as nat + x_i as nat * y[j-1] as nat + A[j-1] as nat) as nat * power(BASE, j-1);
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + uh64(p_2') as nat * power(BASE, j-1) + sint(S')  + uh64(p_1') as nat * power(BASE, j-1) + (x_i as nat * y[j-1] as nat + A[j-1] as nat) as nat * power(BASE, j-1);
            {
                assert x_i as nat * sint(y[..j-1]) + u_i as nat * sint(m[..j-1]) + sint(A[..j-1]) == 
                sint(S') + uh64(p_2') as int * power(BASE, j-1) + uh64(p_1') as int * power(BASE, j-1);
            }
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + x_i as nat * sint(y[..j-1]) + u_i as nat * sint(m[..j-1]) + sint(A[..j-1]) + (x_i as nat * y[j-1] as nat + A[j-1] as nat) as nat * power(BASE, j-1);
            u_i as nat * m[j-1] as nat * power(BASE, j-1) + x_i as nat * sint(y[..j-1]) + u_i as nat * sint(m[..j-1]) + sint(A[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1) + A[j-1] as nat as nat * power(BASE, j-1);
            (u_i as nat * m[j-1] as nat * power(BASE, j-1) + u_i as nat * sint(m[..j-1])) + (x_i as nat * sint(y[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1)) + (sint(A[..j-1]) + A[j-1] as nat as nat * power(BASE, j-1));
            {
                calc == {
                    u_i as nat * m[j-1] as nat * power(BASE, j-1) + u_i as nat * sint(m[..j-1]);
                    u_i as nat * (m[j-1] as nat * power(BASE, j-1) + sint(m[..j-1]));
                    {
                        prefix_interp_lemma_2(m, j);
                    }
                    u_i as nat * sint(m[..j]);
                }
            }
            u_i as nat * sint(m[..j]) + (x_i as nat * sint(y[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1)) + (sint(A[..j-1])  + A[j-1] as nat as nat * power(BASE, j-1));
            {
                calc == { // refactor
                    x_i as nat * sint(y[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1);
                    x_i as nat * (sint(y[..j-1]) + y[j-1] as nat * power(BASE, j-1) );
                    {
                        prefix_interp_lemma_2(y, j);
                    }
                    x_i as nat * sint(y[..j]);
                }
            }
            u_i as nat * sint(m[..j]) + x_i as nat * sint(y[..j]) + (sint(A[..j-1]) + A[j-1] as nat as nat * power(BASE, j-1));
           {
                prefix_interp_lemma_2(A, j);
                assert sint(A[..j-1])  + A[j-1] as nat as nat * power(BASE, j-1) == sint(A[..j]);
            }
            u_i as nat * sint(m[..j]) + x_i as nat * sint(y[..j]) + sint(A[..j]);
        }
    }

    lemma cmm_invarint_lemma_3(
        m: seq<uint32>,
        A: seq<uint32>, 
        x_i: uint32,
        y: seq<uint32>,
        n: nat,
        p_1: uint64,
        p_1': uint64,
        p_2: uint64,
        p_2': uint64,
        u_i: uint32,
        S: seq<uint32>,
        S': seq<uint32>)

        requires |m| == |A| == |y| == |S'| == n;
        requires p_1 as nat == uh64(p_1') as nat + uh64(p_2') as nat;
        requires S == S' + [lh64(p_1), uh64(p_1)];

        requires x_i as nat * sint(y[..n]) + u_i as nat * sint(m[..n]) + sint(A[..n]) == 
            sint(S') + uh64(p_2') as int * power(BASE, n) + uh64(p_1') as int * power(BASE, n);
        ensures sint(S) == 
            x_i as nat * sint(y) + u_i as nat * sint(m) + sint(A);
    {
        calc == {
            sint(S);
            interp(S, n + 2);
            interp(S, n + 1) + uh64(p_1) as nat * power(BASE, n+1);
            word_interp(S, n) + interp(S, n) + uh64(p_1) as nat * power(BASE, n+1);
            {
                prefix_sum_lemma(S, S', n);
            }
            S[n] as nat * power(BASE, n) + sint(S') + uh64(p_1) as nat * power(BASE, n+1);
            lh64(p_1) as nat * power(BASE, n) + sint(S') + uh64(p_1) as nat * power(BASE, n+1);
            lh64(p_1) as nat * power(BASE, n) + uh64(p_1) as nat * power(BASE, n+1) + sint(S') ;
            {
                assert power(BASE, n+1) == BASE * power(BASE, n) by {
                    power_add_one_lemma(BASE, n);
                }
            }
            lh64(p_1) as nat * power(BASE, n) + uh64(p_1) as nat * BASE * power(BASE, n) + sint(S') ;
            {
                assert lh64(p_1) as nat * power(BASE, n) + uh64(p_1) as nat * BASE * power(BASE, n) ==
                    (lh64(p_1) as nat + uh64(p_1) as nat * BASE) * power(BASE, n);
            }
            (lh64(p_1) as nat + uh64(p_1) as nat * BASE) * power(BASE, n) + sint(S');
            {
                split64_lemma(p_1);
            }
            p_1 as nat * power(BASE, n) + sint(S');
            {
                assert p_1 as nat == uh64(p_1') as nat + uh64(p_2') as nat;
            }
            (uh64(p_1') as nat + uh64(p_2') as nat) * power(BASE, n) + sint(S');
            uh64(p_1') as nat * power(BASE, n) + uh64(p_2') as nat * power(BASE, n) + sint(S');
            {
                assert x_i as nat * sint(y[..n]) + u_i as nat * sint(m[..n]) + sint(A[..n]) == 
                    sint(S') + uh64(p_2') as int * power(BASE, n) + uh64(p_1') as int * power(BASE, n);
            }
            x_i as nat * sint(y[..n]) + u_i as nat * sint(m[..n]) + sint(A[..n]);
            {
                assert y == y[..n];
                assert m == m[..n];
                assert A == A[..n];
            }
            x_i as nat * sint(y) + u_i as nat * sint(m) + sint(A);
        }
    }
    
    lemma cmm_divisible_lemma_2(key: pub_key, S: seq<uint32>)
        requires pub_key_valid(key);
        requires |S| == key.len + 2;
        requires S[0] == 0;
        ensures sint(S) == sint(S[1..]) * BASE;
    {
        assert sint(S) % BASE == 0 && sint(S) / BASE == sint(S[1..]) by {
            assert cong(S[0] as int , 0, BASE) by {
                reveal cong();
            } 
            seq_div_base_lemma(S, key.len + 2);
        }
    }

    lemma cmm_ghost_lemma(A': seq<uint32>, S: seq<uint32>, p_1: uint64, n: nat)
        requires |S| == n + 2;
        requires A' == S[1..n+1];
        requires S[n + 1] as int == uh64(p_1) as int;

        ensures uh64(p_1) as nat * power(BASE, n) + sint(A') == sint(S[1..]);
    {
        assert uh64(p_1) as nat * power(BASE, n) + sint(A') == sint(S[1..]) by {
            calc == {
                sint(S[1..]);
                word_interp(S[1..], n) + interp(S[1..], n);
                {
                    prefix_sum_lemma(S[1..], S[1..n+1], n);
                    prefix_sum_lemma(S[1..n+1], A', n);
                }
                word_interp(S[1..], n) + interp(A', n);
                word_interp(S[1..], n) + sint(A');
                uh64(p_1) as nat * power(BASE, n) + sint(A');
            }
        }
    }

    lemma cmm_congruent_lemma_2(key: pub_key, x: seq<uint32>, i: nat, x_i: nat, u_i: nat, A_val: nat, A_val': nat, y_val: nat)
        requires pub_key_valid(key);
        requires i < |x| == key.len && x[i] as int == x_i;

        requires cong(A_val, sint(x[..i]) * y_val * power(key.BASE_INV, i), key.n_val);
        requires cong(A_val' * BASE, x_i * y_val + u_i * key.n_val + A_val, key.n_val);

        ensures cong(A_val', (sint(x[..i]) * y_val * power(key.BASE_INV, i) + x_i * y_val) * key.BASE_INV, key.n_val);
    {
        ghost var ps_inv := power(key.BASE_INV, i);
        var temp := sint(x[..i]) * y_val * ps_inv;

        assert assert_1 : cong(A_val', (A_val + x_i * y_val) * key.BASE_INV, key.n_val) by {
            calc ==> {
                cong(A_val' * BASE, x_i * y_val + u_i * key.n_val + A_val, key.n_val);
                {
                    mod_mul_lemma(u_i, key.n_val, key.n_val);
                    cong_add_lemma_3(x_i * y_val + A_val, u_i * key.n_val, key.n_val);
                    assert cong(x_i * y_val + A_val, x_i * y_val + A_val + u_i * key.n_val, key.n_val);
                    reveal cong();
                }
                cong(A_val' * BASE, x_i * y_val + A_val, key.n_val);
                {
                    cong_mul_lemma_1(A_val' * BASE, x_i * y_val + A_val, key.BASE_INV, key.n_val);
                }
                cong(A_val' * BASE * key.BASE_INV, (x_i * y_val + A_val) * key.BASE_INV, key.n_val);
                {
                    mod_mul_lemma(A_val', BASE,  BASE);
                    mod_div_inv_leamma(A_val' * BASE, BASE, key.BASE_INV, key.n_val);
                    assert cong(A_val' * BASE * key.BASE_INV, A_val', key.n_val);
                    reveal cong();
                }
                cong(A_val', (x_i * y_val + A_val) * key.BASE_INV, key.n_val);
                {
                    assert A_val + x_i * y_val == x_i * y_val + A_val;
                }
                cong(A_val', (A_val + x_i * y_val) * key.BASE_INV, key.n_val);
            }
        }


        assert assert_2: cong((A_val + x_i * y_val) * key.BASE_INV, (temp + x_i * y_val) * key.BASE_INV, key.n_val) by {
            calc ==> {
                cong(A_val, temp, key.n_val);
                {
                    cong_add_lemma_1(A_val, temp, x_i * y_val, key.n_val);
                }
                cong(A_val + x_i * y_val, temp + x_i * y_val, key.n_val);
                {
                    cong_mul_lemma_1(A_val + x_i * y_val, temp + x_i * y_val, key.BASE_INV, key.n_val);
                }
                cong((A_val + x_i * y_val) * key.BASE_INV, (temp + x_i * y_val) * key.BASE_INV, key.n_val);
            }
        }

        assert cong(A_val', (temp + x_i * y_val) * key.BASE_INV, key.n_val) by {
            reveal assert_1;
            reveal assert_2;
            cong_trans_lemma(A_val', (A_val + x_i * y_val) * key.BASE_INV, (temp + x_i * y_val) * key.BASE_INV, key.n_val);
        }
    }

    lemma {:timeLimit 10} cmm_congruent_lemma(key: pub_key, x: seq<uint32>, i: nat, x_i: nat, u_i: nat, A_val: nat, A_val': nat, y_val: nat)
        requires pub_key_valid(key);
        requires i < |x| == key.len && x[i] as int == x_i;

        requires cong(A_val, sint(x[..i]) * y_val * power(key.BASE_INV, i), key.n_val);
        requires cong(A_val' * BASE, x_i * y_val + u_i * key.n_val + A_val, key.n_val);

        ensures cong(A_val', sint(x[..i+1]) * y_val * power(key.BASE_INV, i+1), key.n_val);
    {
        ghost var ps_inv := power(key.BASE_INV, i);

        assert cong(A_val', y_val * sint(x[..i+1]) * ps_inv * key.BASE_INV, key.n_val) by {
            var temp := sint(x[..i]) * y_val * ps_inv;
            var temp2 := (temp + x_i * y_val) * key.BASE_INV;

            assert cong(A_val', temp2, key.n_val) by {
                cmm_congruent_lemma_2(key, x, i, x_i, u_i, A_val, A_val', y_val);
            }

            assert cong(temp2, y_val * sint(x[..i+1]) * ps_inv * key.BASE_INV, key.n_val) by {
                calc == {
                    (temp + x_i * y_val) % key.n_val;
                    {
                        assert temp == sint(x[..i]) * y_val * ps_inv;
                    }
                    (sint(x[..i]) * y_val * ps_inv + x_i * y_val) % key.n_val;
                    (y_val * (sint(x[..i]) * ps_inv + x_i)) % key.n_val;
                    {
                        mont_mul_congruent_aux_lemma_1(x, i, y_val, power(BASE, i), power(key.BASE_INV, i), key.BASE_INV, key.n_val);
                    }
                    (y_val * sint(x[..i+1]) * ps_inv) % key.n_val;
                }
                reveal cong();
                assert cong(temp + x_i * y_val, y_val * sint(x[..i+1]) * ps_inv, key.n_val);
                cong_mul_lemma_1(temp + x_i * y_val, y_val * sint(x[..i+1]) * ps_inv, key.BASE_INV, key.n_val);
            }
            cong_trans_lemma(A_val', temp2, y_val * sint(x[..i+1]) * ps_inv * key.BASE_INV, key.n_val);
        }

        assert cong(A_val', sint(x[..i+1]) * y_val * power(key.BASE_INV, i + 1), key.n_val) by {
            assert ps_inv * key.BASE_INV == power(key.BASE_INV, i + 1) by {
                power_add_one_lemma(key.BASE_INV, i);
            }
            assert y_val * sint(x[..i+1]) * power(key.BASE_INV, i + 1) == sint(x[..i+1]) * y_val * power(key.BASE_INV, i + 1);
        }
    }

    lemma cmm_bounded_lemma_1(
        key: pub_key,
        u_i: uint32,
        x_i: uint32,
        higher: uint32,
        y: seq<uint32>,
        A': seq<uint32>,
        A: seq<uint32>)

        requires pub_key_valid(key);
        requires |A'| == |A| == |y| == key.len;
        requires sint(A) < key.n_val + sint(y);
        requires (higher as nat * key.R + sint(A')) * BASE == 
            x_i as nat * sint(y) + u_i as nat * key.n_val + sint(A);
        ensures (higher as nat * key.R + sint(A')) < (sint(y) + key.n_val);
        ensures higher <= 1;
        ensures (higher == 1 ==> sint(A') < key.n_val);
    {
        assert (higher as nat * key.R + sint(A')) * BASE < BASE * (sint(y) + key.n_val) by {
            assert (higher as nat * key.R + sint(A')) * BASE <
                (x_i as nat + 1) * sint(y) + (u_i as nat + 1) * key.n_val by {
                    assert sint(A) < key.n_val + sint(y);
            }

            calc <= {
                (x_i as nat + 1) * sint(y) + (u_i as nat + 1) * key.n_val;
                {
                    assert x_i as nat + 1 <= BASE;
                }
                BASE * sint(y) + (u_i as nat + 1) * key.n_val;
                {
                    assert u_i as nat + 1 <= BASE;
                }
                BASE * sint(y) + BASE * key.n_val;
                BASE * (sint(y) + key.n_val);
            }
        }

        assert (higher as nat * key.R + sint(A')) < (sint(y) + key.n_val);

       if higher > 1 {
            assert higher >= 2;
            assert higher as nat * key.R + sint(A') >= 2 * key.R + sint(A');
            
            assert sint(y) < key.R by {
                sint_upper_bound_lemma(y, key.len);
            }

            assert key.n_val < key.R;
            assert false;
        }

        if higher == 1 && sint(A') >= key.n_val {
            assert key.R + sint(A') < sint(y) + key.n_val;
            sint_upper_bound_lemma(y, key.len);
        }
    }
}