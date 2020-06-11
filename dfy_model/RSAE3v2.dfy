include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"
include "SeqInt.dfy"
include "RSAE3v1.dfy"
include "RSALemmas.dfy"

module RSAE3v2 {
    import opened NativeTypes
    import opened Powers
    import opened Congruences
    import opened SeqInt
    import opened RSAE3v1
    import opened RSALemmas

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

        ensures x_i as nat * seq_interp(y[..1]) + u_i as nat * seq_interp(m[..1]) + seq_interp(A[..1]) as nat == 
            uh64(p_2) as int * power(BASE, 1) + uh64(p_1) as int * power(BASE, 1);
    {
        calc == {
            x_i as nat * seq_interp(y[..1]) + u_i as nat * seq_interp(m[..1]) + seq_interp(A[..1]);
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

        requires x_i as nat * seq_interp(y[..j-1]) + u_i as nat * seq_interp(m[..j-1]) + seq_interp(A[..j-1]) == 
                seq_interp(S') + uh64(p_2') as int * power(BASE, j-1) + uh64(p_1') as int * power(BASE, j-1);
        requires p_1 as nat == uh64(p_1') as nat + x_i as nat * y[j-1] as nat + A[j-1] as nat;
        requires p_2 as nat == uh64(p_2') as nat + u_i as nat * m[j-1] as nat + lh64(p_1) as nat;

        ensures u_i as nat * seq_interp(m[..j]) + x_i as nat * seq_interp(y[..j]) + seq_interp(A[..j]) == 
            seq_interp(S) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
    {
        calc == {
            seq_interp(S) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
            lh64(p_2) as nat * power(BASE, j-1) + interp(S, j-1) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
            {
                prefix_sum_lemma(S, S', j-1);
            }
            lh64(p_2) as nat * power(BASE, j-1) + seq_interp(S') + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
            {
                power_add_one_lemma(BASE, j - 1);
                assert uh64(p_2) as int * power(BASE, j) == uh64(p_2) as int * BASE * power(BASE, j - 1);
            }
            lh64(p_2) as nat * power(BASE, j-1) + seq_interp(S') + uh64(p_2) as int * BASE * power(BASE, j - 1) + uh64(p_1) as int * power(BASE, j);
            lh64(p_2) as nat * power(BASE, j-1) + uh64(p_2) as int * BASE * power(BASE, j - 1 ) + seq_interp(S') + uh64(p_1) as int * power(BASE, j);
            {
                assert lh64(p_2) as nat * power(BASE, j-1) + uh64(p_2) as int * BASE * power(BASE, j - 1) == 
                    (lh64(p_2) as nat + uh64(p_2) as int * BASE) * power(BASE, j - 1);
            }
            (lh64(p_2) as int  + uh64(p_2) as int * BASE) * power(BASE, j-1) + seq_interp(S') + uh64(p_1) as int * power(BASE, j);
            {
                split64_lemma(p_2);
            }
            p_2 as int * power(BASE, j-1) + seq_interp(S') + uh64(p_1) as int * power(BASE, j);
            {
                assert p_2 as nat == uh64(p_2') as nat + u_i as nat * m[j-1] as nat + lh64(p_1) as nat;
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat + lh64(p_1) as nat) * power(BASE, j-1) + seq_interp(S') + uh64(p_1) as int * power(BASE, j);
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + lh64(p_1) as nat * power(BASE, j-1) + seq_interp(S') + uh64(p_1) as int * power(BASE, j);
            {
                power_add_one_lemma(BASE, j - 1);
                assert uh64(p_1) as int * power(BASE, j) == uh64(p_1) as int * BASE * power(BASE, j - 1);
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + lh64(p_1) as nat * power(BASE, j-1) + seq_interp(S') +  uh64(p_1) as int * BASE * power(BASE, j - 1);
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + seq_interp(S') + lh64(p_1) as nat * power(BASE, j-1) +  uh64(p_1) as int * BASE * power(BASE, j - 1);
            {
                assert lh64(p_1) as nat * power(BASE, j-1) +  uh64(p_1) as int * BASE * power(BASE, j - 1) == (lh64(p_1) as nat +  uh64(p_1) as int * BASE) * power(BASE, j - 1);
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + seq_interp(S')  + (lh64(p_1) as nat + uh64(p_1) as nat * BASE)* power(BASE, j-1);
            {
                split64_lemma(p_1);
            }
            (uh64(p_2') as nat + u_i as nat * m[j-1] as nat) * power(BASE, j-1) + seq_interp(S')  + p_1 as nat * power(BASE, j-1);
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + uh64(p_2') as nat * power(BASE, j-1) + seq_interp(S')  + p_1 as nat * power(BASE, j-1);
            {
                assert p_1 as nat == uh64(p_1') as nat + x_i as nat * y[j-1] as nat + A[j-1] as nat;
            }
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + uh64(p_2') as nat * power(BASE, j-1) + seq_interp(S')  + (uh64(p_1') as nat + x_i as nat * y[j-1] as nat + A[j-1] as nat) as nat * power(BASE, j-1);
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + uh64(p_2') as nat * power(BASE, j-1) + seq_interp(S')  + uh64(p_1') as nat * power(BASE, j-1) + (x_i as nat * y[j-1] as nat + A[j-1] as nat) as nat * power(BASE, j-1);
            {
                assert x_i as nat * seq_interp(y[..j-1]) + u_i as nat * seq_interp(m[..j-1]) + seq_interp(A[..j-1]) == 
                seq_interp(S') + uh64(p_2') as int * power(BASE, j-1) + uh64(p_1') as int * power(BASE, j-1);
            }
            (u_i as nat * m[j-1] as nat) * power(BASE, j-1) + x_i as nat * seq_interp(y[..j-1]) + u_i as nat * seq_interp(m[..j-1]) + seq_interp(A[..j-1]) + (x_i as nat * y[j-1] as nat + A[j-1] as nat) as nat * power(BASE, j-1);
            u_i as nat * m[j-1] as nat * power(BASE, j-1) + x_i as nat * seq_interp(y[..j-1]) + u_i as nat * seq_interp(m[..j-1]) + seq_interp(A[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1) + A[j-1] as nat as nat * power(BASE, j-1);
            (u_i as nat * m[j-1] as nat * power(BASE, j-1) + u_i as nat * seq_interp(m[..j-1])) + (x_i as nat * seq_interp(y[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1)) + (seq_interp(A[..j-1]) + A[j-1] as nat as nat * power(BASE, j-1));
            {
                calc == {
                    u_i as nat * m[j-1] as nat * power(BASE, j-1) + u_i as nat * seq_interp(m[..j-1]);
                    u_i as nat * (m[j-1] as nat * power(BASE, j-1) + seq_interp(m[..j-1]));
                    {
                        prefix_interp_lemma_2(m, j);
                    }
                    u_i as nat * seq_interp(m[..j]);
                }
            }
            u_i as nat * seq_interp(m[..j]) + (x_i as nat * seq_interp(y[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1)) + (seq_interp(A[..j-1])  + A[j-1] as nat as nat * power(BASE, j-1));
            {
                calc == { // refactor
                    x_i as nat * seq_interp(y[..j-1]) + x_i as nat * y[j-1] as nat * power(BASE, j-1);
                    x_i as nat * (seq_interp(y[..j-1]) + y[j-1] as nat * power(BASE, j-1) );
                    {
                        prefix_interp_lemma_2(y, j);
                    }
                    x_i as nat * seq_interp(y[..j]);
                }
            }
            u_i as nat * seq_interp(m[..j]) + x_i as nat * seq_interp(y[..j]) + (seq_interp(A[..j-1]) + A[j-1] as nat as nat * power(BASE, j-1));
           {
                prefix_interp_lemma_2(A, j);
                assert seq_interp(A[..j-1])  + A[j-1] as nat as nat * power(BASE, j-1) == seq_interp(A[..j]);
            }
            u_i as nat * seq_interp(m[..j]) + x_i as nat * seq_interp(y[..j]) + seq_interp(A[..j]);
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

        requires x_i as nat * seq_interp(y[..n]) + u_i as nat * seq_interp(m[..n]) + seq_interp(A[..n]) == 
            seq_interp(S') + uh64(p_2') as int * power(BASE, n) + uh64(p_1') as int * power(BASE, n);
        ensures seq_interp(S) == 
            x_i as nat * seq_interp(y) + u_i as nat * seq_interp(m) + seq_interp(A);
    {
        calc == {
            seq_interp(S);
            interp(S, n + 2);
            interp(S, n + 1) + uh64(p_1) as nat * power(BASE, n+1);
            word_interp(S, n) + interp(S, n) + uh64(p_1) as nat * power(BASE, n+1);
            {
                prefix_sum_lemma(S, S', n);
            }
            S[n] as nat * power(BASE, n) + seq_interp(S') + uh64(p_1) as nat * power(BASE, n+1);
            lh64(p_1) as nat * power(BASE, n) + seq_interp(S') + uh64(p_1) as nat * power(BASE, n+1);
            lh64(p_1) as nat * power(BASE, n) + uh64(p_1) as nat * power(BASE, n+1) + seq_interp(S') ;
            {
                assert power(BASE, n+1) == BASE * power(BASE, n) by {
                    power_add_one_lemma(BASE, n);
                }
            }
            lh64(p_1) as nat * power(BASE, n) + uh64(p_1) as nat * BASE * power(BASE, n) + seq_interp(S') ;
            {
                assert lh64(p_1) as nat * power(BASE, n) + uh64(p_1) as nat * BASE * power(BASE, n) ==
                    (lh64(p_1) as nat + uh64(p_1) as nat * BASE) * power(BASE, n);
            }
            (lh64(p_1) as nat + uh64(p_1) as nat * BASE) * power(BASE, n) + seq_interp(S');
            {
                split64_lemma(p_1);
            }
            p_1 as nat * power(BASE, n) + seq_interp(S');
            {
                assert p_1 as nat == uh64(p_1') as nat + uh64(p_2') as nat;
            }
            (uh64(p_1') as nat + uh64(p_2') as nat) * power(BASE, n) + seq_interp(S');
            uh64(p_1') as nat * power(BASE, n) + uh64(p_2') as nat * power(BASE, n) + seq_interp(S');
            {
                assert x_i as nat * seq_interp(y[..n]) + u_i as nat * seq_interp(m[..n]) + seq_interp(A[..n]) == 
                    seq_interp(S') + uh64(p_2') as int * power(BASE, n) + uh64(p_1') as int * power(BASE, n);
            }
            x_i as nat * seq_interp(y[..n]) + u_i as nat * seq_interp(m[..n]) + seq_interp(A[..n]);
            {
                assert y == y[..n];
                assert m == m[..n];
                assert A == A[..n];
            }
            x_i as nat * seq_interp(y) + u_i as nat * seq_interp(m) + seq_interp(A);
        }
    }
    
    lemma cmm_divisible_lemma_2(key: pub_key, S: seq<uint32>)
        requires pub_key_valid(key);
        requires |S| == key.len + 2;
        requires S[0] == 0;
        ensures seq_interp(S) == seq_interp(S[1..]) * BASE;
    {
        assert seq_interp(S) % BASE == 0 && seq_interp(S) / BASE == seq_interp(S[1..]) by {
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

        ensures uh64(p_1) as nat * power(BASE, n) + seq_interp(A') == seq_interp(S[1..]);
    {
        assert uh64(p_1) as nat * power(BASE, n) + seq_interp(A') == seq_interp(S[1..]) by {
            calc == {
                seq_interp(S[1..]);
                word_interp(S[1..], n) + interp(S[1..], n);
                {
                    prefix_sum_lemma(S[1..], S[1..n+1], n);
                    prefix_sum_lemma(S[1..n+1], A', n);
                }
                word_interp(S[1..], n) + interp(A', n);
                word_interp(S[1..], n) + seq_interp(A');
                uh64(p_1) as nat * power(BASE, n) + seq_interp(A');
            }
        }
    }

    lemma cmm_congruent_lemma_2(key: pub_key, x: seq<uint32>, i: nat, x_i: nat, u_i: nat, A_val: nat, A_val': nat, y_val: nat)
        requires pub_key_valid(key);
        requires i < |x| == key.len && x[i] as int == x_i;

        requires cong(A_val, seq_interp(x[..i]) * y_val * power(key.BASE_INV, i), key.n_val);
        requires cong(A_val' * BASE, x_i * y_val + u_i * key.n_val + A_val, key.n_val);

        ensures cong(A_val', (seq_interp(x[..i]) * y_val * power(key.BASE_INV, i) + x_i * y_val) * key.BASE_INV, key.n_val);
    {
        ghost var ps_inv := power(key.BASE_INV, i);
        var temp := seq_interp(x[..i]) * y_val * ps_inv;

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

        requires cong(A_val, seq_interp(x[..i]) * y_val * power(key.BASE_INV, i), key.n_val);
        requires cong(A_val' * BASE, x_i * y_val + u_i * key.n_val + A_val, key.n_val);

        ensures cong(A_val', seq_interp(x[..i+1]) * y_val * power(key.BASE_INV, i+1), key.n_val);
    {
        ghost var ps_inv := power(key.BASE_INV, i);

        assert cong(A_val', y_val * seq_interp(x[..i+1]) * ps_inv * key.BASE_INV, key.n_val) by {
            var temp := seq_interp(x[..i]) * y_val * ps_inv;
            var temp2 := (temp + x_i * y_val) * key.BASE_INV;

            assert cong(A_val', temp2, key.n_val) by {
                cmm_congruent_lemma_2(key, x, i, x_i, u_i, A_val, A_val', y_val);
            }

            assert cong(temp2, y_val * seq_interp(x[..i+1]) * ps_inv * key.BASE_INV, key.n_val) by {
                calc == {
                    (temp + x_i * y_val) % key.n_val;
                    {
                        assert temp == seq_interp(x[..i]) * y_val * ps_inv;
                    }
                    (seq_interp(x[..i]) * y_val * ps_inv + x_i * y_val) % key.n_val;
                    (y_val * (seq_interp(x[..i]) * ps_inv + x_i)) % key.n_val;
                    {
                        mont_mul_congruent_aux_lemma_1(x, i, y_val, power(BASE, i), power(key.BASE_INV, i), key.BASE_INV, key.n_val);
                    }
                    (y_val * seq_interp(x[..i+1]) * ps_inv) % key.n_val;
                }
                reveal cong();
                assert cong(temp + x_i * y_val, y_val * seq_interp(x[..i+1]) * ps_inv, key.n_val);
                cong_mul_lemma_1(temp + x_i * y_val, y_val * seq_interp(x[..i+1]) * ps_inv, key.BASE_INV, key.n_val);
            }
            cong_trans_lemma(A_val', temp2, y_val * seq_interp(x[..i+1]) * ps_inv * key.BASE_INV, key.n_val);
        }

        assert cong(A_val', seq_interp(x[..i+1]) * y_val * power(key.BASE_INV, i + 1), key.n_val) by {
            assert ps_inv * key.BASE_INV == power(key.BASE_INV, i + 1) by {
                power_add_one_lemma(key.BASE_INV, i);
            }
            assert y_val * seq_interp(x[..i+1]) * power(key.BASE_INV, i + 1) == seq_interp(x[..i+1]) * y_val * power(key.BASE_INV, i + 1);
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
        requires seq_interp(A) < key.n_val + seq_interp(y);
        requires (higher as nat * key.R + seq_interp(A')) * BASE == 
            x_i as nat * seq_interp(y) + u_i as nat * key.n_val + seq_interp(A);
        ensures (higher as nat * key.R + seq_interp(A')) < (seq_interp(y) + key.n_val);
        ensures higher <= 1;
        ensures (higher == 1 ==> seq_interp(A') < key.n_val);
    {
        assert (higher as nat * key.R + seq_interp(A')) * BASE < BASE * (seq_interp(y) + key.n_val) by {
            assert (higher as nat * key.R + seq_interp(A')) * BASE <
                (x_i as nat + 1) * seq_interp(y) + (u_i as nat + 1) * key.n_val by {
                    assert seq_interp(A) < key.n_val + seq_interp(y);
            }

            calc <= {
                (x_i as nat + 1) * seq_interp(y) + (u_i as nat + 1) * key.n_val;
                {
                    assert x_i as nat + 1 <= BASE;
                }
                BASE * seq_interp(y) + (u_i as nat + 1) * key.n_val;
                {
                    assert u_i as nat + 1 <= BASE;
                }
                BASE * seq_interp(y) + BASE * key.n_val;
                BASE * (seq_interp(y) + key.n_val);
            }
        }

        assert (higher as nat * key.R + seq_interp(A')) < (seq_interp(y) + key.n_val);

       if higher > 1 {
            assert higher >= 2;
            assert higher as nat * key.R + seq_interp(A') >= 2 * key.R + seq_interp(A');
            
            assert seq_interp(y) < key.R by {
                seq_interp_upper_bound_lemma(y, key.len);
            }

            assert key.n_val < key.R;
            assert false;
        }

        if higher == 1 && seq_interp(A') >= key.n_val {
            assert key.R + seq_interp(A') < seq_interp(y) + key.n_val;
            seq_interp_upper_bound_lemma(y, key.len);
        }
    }

/*
    uint64_t p_1 = (uint64_t)x_i * y[0] + A[0];
    uint32_t u_i = (uint32_t)p_1 * m';
    uint64_t p_2 = (uint64_t)u_i * m[0] + (uint32_t)p_1;

    int i;
    for (i = 1; i < len; ++i) {
        p_1 = (p_1 >> 32) + (uint64_t)x_i * y[i] + A[i];
        p_2 = (p_2 >> 32) + (uint64_t)u_i * m[i] + (uint32_t)p_1;
        A[i - 1] = (uint32_t)p_2;
    }
    p_1 = (p_1 >> 32) + (p_2 >> 32);
    A[i - 1] = (uint32_t)p_1;
    if (p_1 >> 32) {
        subM(key, A);
    }
*/

    method montMulAdd(
        key: pub_key,
        A: seq<uint32>, 
        x_i: uint32,
        y: seq<uint32>,
        ghost i: nat,
        ghost x: seq<uint32>)

        returns (A': seq<uint32>)
        requires pub_key_valid(key);

        requires |A| == |y| == |x| == key.len;
        requires i < |x| == key.len && x[i] == x_i;
        requires cong(seq_interp(A), seq_interp(x[..i]) * seq_interp(y) * power(key.BASE_INV, i), key.n_val);

        requires seq_interp(A) < key.n_val + seq_interp(y);
    
        ensures cong(seq_interp(A'), seq_interp(x[..i+1]) * seq_interp(y) * power(key.BASE_INV, i+1), key.n_val);
        ensures |A'| == key.len;
        ensures seq_interp(A') < seq_interp(y) + key.n_val;
    {
        single_digit_mul_lemma(x_i, y[0], A[0]);
        var p_1 :uint64 := x_i as uint64 * y[0] as uint64 + A[0] as uint64;
        var u_i :uint32 := ((lh64(p_1) as nat * key.m' as nat) % BASE) as uint32;

        single_digit_mul_lemma(u_i, key.m[0], lh64(p_1));
        var p_2 :uint64 := u_i as uint64 * key.m[0] as uint64 + lh64(p_1) as uint64;

        assert cong(p_2 as int, 0, BASE) by {
            cmm_divisible_lemma_1(p_1 as nat, p_2 as nat, x_i as nat, y[0] as nat, A[0] as nat, u_i as nat, key.m' as nat, key.m[0] as nat);
        }

        ghost var S := [0];
        A' := zero_seq_int(key.len);

        var j := 1;

        assert x_i as nat * seq_interp(y[..j]) + u_i as nat * seq_interp(key.m[..j]) + seq_interp(A[..1]) as nat == 
            uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j)
        by {
            cmm_invarint_lemma_1(key.m, A, x_i, y, key.len, p_1, p_2, u_i);
        }

        while j != key.len
            decreases key.len - j;
            invariant 0 < j <= key.len;
            invariant |A'| == key.len;
            invariant |S| == j;
            invariant S[0] == 0;
            invariant x_i as nat * seq_interp(y[..j]) + u_i as nat * seq_interp(key.m[..j]) + seq_interp(A[..j]) == 
                seq_interp(S) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
            invariant forall k :: 0 <= k < j - 1 ==> A'[k] == S[k + 1];
        {
            ghost var S', j', p_1', p_2' := S, j, p_1, p_2;

            p_1 := uh64(p_1) as uint64 + x_i as uint64 * y[j] as uint64 + A[j] as uint64;
            p_2 := uh64(p_2) as uint64 + u_i as uint64 * key.m[j] as uint64 + lh64(p_1) as uint64;
            A' := A'[j-1 := lh64(p_2)];

            S := S + [lh64(p_2)];
            j := j + 1;

            cmm_invarint_lemma_2(key.m, A, x_i, y, key.len, p_1, p_1', p_2, p_2', u_i, j, S, S');
        }

        ghost var S', p_1', p_2' := S, p_1, p_2;

        var temp := uh64(p_1) as uint64 + uh64(p_2) as uint64;
        A' := A'[j-1 := lh64(temp)];
        S := S + [lh64(temp), uh64(temp)];

        assert (uh64(temp) as nat * key.R + seq_interp(A')) * BASE == 
            x_i as nat * seq_interp(y) + u_i as nat * key.n_val + seq_interp(A)
        by {
            assert seq_interp(S) == x_i as nat * seq_interp(y) + u_i as nat * key.n_val + seq_interp(A) by {
                cmm_invarint_lemma_3(key.m, A, x_i, y, key.len, temp, p_1', p_2, p_2', u_i, S, S');
            }

            assert seq_interp(S) == seq_interp(S[1..]) * BASE by {
                cmm_divisible_lemma_2(key, S);
            }

            assert uh64(temp) as nat * key.R + seq_interp(A') == seq_interp(S[1..]) by {
                assert A' == A'[0..key.len] == S[1..key.len+1] by {
                    assert forall k :: 0 <= k < key.len ==> A'[k] == S[k + 1];
                }
                cmm_ghost_lemma(A', S, temp, key.len);
            }
        }

        assert uh64(temp) as nat * key.R + seq_interp(A') < seq_interp(y) + key.n_val
            && uh64(temp) <= 1 
            && (uh64(temp) == 1 ==> seq_interp(A') < key.n_val)
        by {
            cmm_bounded_lemma_1(key, u_i, x_i, uh64(temp), y, A', A);
        }

        ghost var result := x_i as nat * seq_interp(y) + u_i as nat * key.n_val + seq_interp(A);

        if uh64(temp) != 0 {
            var b, A'' := seq_sub(A', key.m);
            calc == {
                result;
                {
                    assert uh64(temp) == 1;
                }
                (key.R + seq_interp(A')) * BASE;
                {
                    assert seq_interp(A') + key.R == seq_interp(A'') + key.n_val;
                }
                (seq_interp(A'') + key.n_val) * BASE;
            }
            
            assert cong((seq_interp(A'') + key.n_val) * BASE, result, key.n_val) by {
                reveal cong();
            }

            calc ==> {
                cong((seq_interp(A'') + key.n_val) * BASE, result, key.n_val);
                {
                    mod_mul_lemma(-BASE, key.n_val, key.n_val);
                    cong_add_lemma_3((seq_interp(A'') + key.n_val) * BASE, -key.n_val * BASE,  key.n_val);
                    reveal cong();
                }
                cong((seq_interp(A'') + key.n_val) * BASE - key.n_val * BASE, result, key.n_val);
                {
                    assert (seq_interp(A'') + key.n_val) * BASE - key.n_val * BASE == seq_interp(A'') * BASE;
                }
                cong(seq_interp(A'') * BASE, result, key.n_val);
            }

            assert cong(seq_interp(A'') * BASE, result, key.n_val);

            A' := A'';
        } else {
            assert seq_interp(A') < seq_interp(y) + key.n_val;
            assert cong(seq_interp(A') * BASE, result, key.n_val) by {
                assert seq_interp(A') * BASE == result;
                reveal cong();
            }
        }

        assert cong(seq_interp(A'), seq_interp(x[..i+1]) * seq_interp(y) * power(key.BASE_INV, i+1), key.n_val) by {
            cmm_congruent_lemma(key, x, i, x_i as nat, u_i as nat, seq_interp(A), seq_interp(A'), seq_interp(y));
        }
    }

    method montMul(key: pub_key, x: seq<uint32>, y: seq<uint32>)
        returns (A: seq<uint32>)

        requires pub_key_valid(key);
        requires |x| == |y| == key.len;

        ensures cong(seq_interp(A), seq_interp(x) * seq_interp(y) * key.R_INV, key.n_val);
        ensures seq_interp(A) < key.n_val + seq_interp(y);
        ensures |A| == key.len;
    {
        A  := zero_seq_int(key.len);
        assert seq_interp(A) == 0;

        ghost var y_val := seq_interp(y);

        var i := 0;

        assert cong(seq_interp(A), seq_interp(x[..i]) * seq_interp(y) * power(key.BASE_INV, i), key.n_val) by {
            assert seq_interp(A) == seq_interp(x[..i]) * seq_interp(y) * power(key.BASE_INV, i);
            reveal cong();
        }
        
        while i != key.len
            decreases key.len - i;
            invariant i <= |x|;
            invariant |A| == key.len;

            invariant cong(seq_interp(A), seq_interp(x[..i]) * seq_interp(y) * power(key.BASE_INV, i), key.n_val);
            invariant seq_interp(A) < key.n_val + seq_interp(y);
        {
            A := montMulAdd(key, A, x[i], y, i, x);
            i := i + 1;
        }

        assert cong(seq_interp(A), seq_interp(x) * seq_interp(y) * power(key.BASE_INV, i), key.n_val) by {
            assert x == x[..key.len];
        }

        assert cong(seq_interp(A), seq_interp(x) * seq_interp(y) * key.R_INV, key.n_val);
    }

    lemma R_inv_cancel_lemma(key: pub_key, v: int)
        requires pub_key_valid(key);
        ensures cong(v * key.R * key.R_INV, v, key.n_val);
    {
        calc ==> {
            cong(key.R * key.R_INV, 1, key.n_val);
            {
                cong_mul_lemma_1(key.R * key.R_INV, 1, v, key.n_val);
            }
            cong(key.R * key.R_INV * v, v, key.n_val);
        }
    }

    lemma mod_pow3_congruent_lemma_1(key: pub_key, a: int, ar: int, aar: int, aaa: int, rr: int)
        requires pub_key_valid(key);
        requires cong(rr, key.R * key.R, key.n_val);
        requires cong(ar, a * rr * key.R_INV, key.n_val);
        requires cong(aar, ar * ar * key.R_INV, key.n_val);
        requires cong(aaa, aar * a * key.R_INV, key.n_val);
        ensures cong(aaa, a * a * a, key.n_val);
    {
        assert cong(aar, key.R * a * a, key.n_val) by {
            mod_pow3_congruent_lemma_2(key, a, ar, aar, rr);
        }

        assert cong(aar * key.R_INV, a * a, key.n_val) by {
            assert cong(aar * key.R_INV, key.R * a * a * key.R_INV, key.n_val) by {
                cong_mul_lemma_1(aar, key.R * a * a, key.R_INV, key.n_val);
            }
            assert cong(key.R * a * a  *  key.R_INV, a * a, key.n_val) by {
                R_inv_cancel_lemma(key, a * a);
            }
            cong_trans_lemma(aar * key.R_INV, key.R * a * a * key.R_INV, a * a, key.n_val);
        }

        assert cong(aaa, a * a * a, key.n_val) by {
            assert cong(aaa, aar * a * key.R_INV, key.n_val);
            assert cong(aar * a * key.R_INV, a * a * a, key.n_val) by {
                cong_mul_lemma_1(aar * key.R_INV, a * a, a, key.n_val);
            }
            cong_trans_lemma(aaa, aar * a * key.R_INV, a * a * a, key.n_val);
        }
        assert cong(aaa, a * a * a, key.n_val);
    }

    lemma mod_pow3_congruent_lemma_2(key: pub_key, a: int, ar: int, aar: int, rr: int)
        requires pub_key_valid(key);
        requires cong(rr, key.R * key.R, key.n_val);
        requires cong(ar, a * rr * key.R_INV, key.n_val);
        requires cong(aar, ar * ar * key.R_INV, key.n_val);
        ensures cong(aar, key.R * a * a, key.n_val);
    {
        assert cong(ar, key.R * a, key.n_val) && cong(ar * key.R_INV, a, key.n_val) by {
            mod_pow3_congruent_lemma_3(key, a, ar, aar, rr);
        }

        assert cong_a4: cong(aar, ar * a, key.n_val) by {
            calc ==> {
                cong(ar * key.R_INV, a, key.n_val);
                {
                    cong_mul_lemma_1(ar * key.R_INV, a, ar, key.n_val);
                }
                cong( ar * ar * key.R_INV, ar * a, key.n_val);
                {
                    assert cong(aar,  ar * ar * key.R_INV, key.n_val);
                    cong_trans_lemma(aar,  ar * ar * key.R_INV, ar * a, key.n_val);
                }
                cong(aar, ar * a, key.n_val);            
            }
        }

        assert cong(aar, key.R * a * a, key.n_val) by {
            assert cong(ar * a, key.R * a * a, key.n_val) by {
                assert cong(ar, key.R * a, key.n_val);
                cong_mul_lemma_1(ar, key.R * a, a, key.n_val);
            }
            reveal cong_a4;
            cong_trans_lemma(aar, ar * a, key.R * a * a, key.n_val);
        }
    }

    lemma mod_pow3_congruent_lemma_3(key: pub_key, a: int, ar: int, aar: int, rr: int)
        requires pub_key_valid(key);
        requires cong(rr, key.R * key.R, key.n_val);
        requires cong(ar, a * rr * key.R_INV, key.n_val);
        requires cong(aar, ar * ar * key.R_INV, key.n_val);
        ensures cong(ar, key.R * a, key.n_val);
        ensures cong(ar * key.R_INV, a, key.n_val);
    {
        assert cong_a1: cong(rr * a * key.R_INV, key.R * a, key.n_val) by {
            assert cong(rr, key.R * key.R, key.n_val);
            calc ==> {
                cong(rr, key.R * key.R, key.n_val);
                {
                    cong_mul_lemma_1(rr, key.R * key.R, a * key.R_INV, key.n_val);
                }
                cong(rr * a * key.R_INV, key.R * key.R * a * key.R_INV, key.n_val);
                {
                    R_inv_cancel_lemma(key, key.R * a);
                    cong_trans_lemma(rr * a * key.R_INV,
                        key.R * key.R * a * key.R_INV,
                        key.R * a, key.n_val);
                }
                cong(rr * a * key.R_INV, key.R * a, key.n_val);
            }
        }

        assert cong(ar, key.R * a, key.n_val) by {
            assert cong(ar, a * rr * key.R_INV, key.n_val);
            reveal cong_a1;
            cong_trans_lemma(ar, a * rr * key.R_INV, key.R * a, key.n_val);
        }

        assert cong(ar * key.R_INV, a, key.n_val) by {
            assert cong(ar * key.R_INV, key.R * a * key.R_INV, key.n_val) by {
                cong_mul_lemma_1(ar, key.R * a, key.R_INV, key.n_val);
            }
            assert cong(key.R * a * key.R_INV, a, key.n_val) by {
                R_inv_cancel_lemma(key, a);
            }
            cong_trans_lemma(ar * key.R_INV, key.R * a * key.R_INV, a, key.n_val);
        }

        assert cong(ar, key.R * a, key.n_val);
        assert cong(ar * key.R_INV, a, key.n_val);
    }

    method modpow3(key: pub_key, a: seq<uint32>) 
        returns (aaa: seq<uint32>)

        requires pub_key_valid(key);
        requires 0 <= seq_interp(a) < key.n_val; 
        requires |a| == key.len;
        ensures seq_interp(aaa) == power(seq_interp(a), 3) % key.n_val;
        ensures |aaa| == key.len;
    {
        var aR := montMul(key, a, key.RR); /* aR = a * RR / R mod M   */
        var aaR := montMul(key, aR, aR); /* aaR = aR * aR / R mod M */
        aaa := montMul(key, aaR, a); /* aaa = aaR * a / R mod M */

        ghost var aaa_val := seq_interp(aaa);
        ghost var a_val := seq_interp(a);

        mod_pow3_congruent_lemma_1(key, a_val, seq_interp(aR), seq_interp(aaR), aaa_val, seq_interp(key.RR));

        var geq := seq_geq(aaa, key.m);

        if geq {
            var _, temp := seq_sub(aaa, key.m);
            ghost var temp_val := seq_interp(temp);
            
            assert cong(aaa_val, temp_val, key.n_val) by {
                assert temp_val == aaa_val - key.n_val;
                cong_add_lemma_3(aaa_val, - key.n_val, key.n_val);
            }
            cong_trans_lemma(temp_val, aaa_val, a_val * a_val * a_val, key.n_val);

            aaa := temp;
        }

        assert seq_interp(aaa) == (a_val * a_val * a_val) % key.n_val by {
            assert 0 <= seq_interp(aaa) < key.n_val;
            assert cong(seq_interp(aaa), a_val * a_val * a_val, key.n_val);
            cong_remainder_lemma(seq_interp(aaa), a_val * a_val * a_val, key.n_val);
        }

        assert (a_val * a_val * a_val == power(a_val, 3)) by {
            reveal power();
        }
    }

    method RSA_e_3_verify(key: pub_key, signature: seq<uint32>, sha: seq<uint32>, ghost rsa: rsa_params)
        returns (x : bool)

        requires pub_key_connect_valid(rsa, key);
        requires |signature| == |sha| == key.len;
        requires 0 <= seq_interp(signature) < key.n_val;
        requires 0 <= seq_interp(sha) < key.n_val;

        ensures x <==> seq_interp(signature) == power(seq_interp(sha), rsa.d) % key.n_val;
    {
        var buf := modpow3(key, signature);
        var i := 0;

        ghost var s := seq_interp(signature);
        ghost var m := seq_interp(sha);

        while i < key.len
            decreases key.len - i;
            invariant 0 <= i <= key.len;
            invariant buf[..i] == sha[..i];
        {
            if buf[i] != sha[i] {
                assert (s != power(m, rsa.d) % rsa.n) by {
                    assert seq_interp(buf) != m by {
                        assert buf != sha;
                        neq_lemma(buf, sha, key.len);
                    }
                    rsa_signature_lemma(rsa, m, s);
                }
                return false;
            }
            i := i + 1;
        }

        assert buf == sha;
        assert (s == power(m, rsa.d) % rsa.n) by {
            assert (power(s, rsa.e) % rsa.n == m);
            rsa_signature_lemma(rsa, m, s);
        }
        return true;
    }
}