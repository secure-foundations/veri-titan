include "NativeTypes.dfy"
include "powers.dfy"
include "congruences.dfy"
include "SeqInt.dfy"
include "RSALemmas.dfy"
include "MMLemmas.dfy"

module RSAE3 {
    import opened NativeTypes
    import opened powers
    import opened congruences
    import opened SeqInt
    import opened RSALemmas
    import opened MMLemmas

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
        requires cong(sint(A), sint(x[..i]) * sint(y) * power(key.BASE_INV, i), key.n_val);

        requires sint(A) < key.n_val + sint(y);
    
        ensures cong(sint(A'), sint(x[..i+1]) * sint(y) * power(key.BASE_INV, i+1), key.n_val);
        ensures |A'| == key.len;
        ensures sint(A') < sint(y) + key.n_val;
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

        assert x_i as nat * sint(y[..j]) + u_i as nat * sint(key.m[..j]) + sint(A[..1]) as nat == 
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
            invariant x_i as nat * sint(y[..j]) + u_i as nat * sint(key.m[..j]) + sint(A[..j]) == 
                sint(S) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);
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

        assert (uh64(temp) as nat * key.R + sint(A')) * BASE == 
            x_i as nat * sint(y) + u_i as nat * key.n_val + sint(A)
        by {
            assert sint(S) == x_i as nat * sint(y) + u_i as nat * key.n_val + sint(A) by {
                cmm_invarint_lemma_3(key.m, A, x_i, y, key.len, temp, p_1', p_2, p_2', u_i, S, S');
            }

            assert sint(S) == sint(S[1..]) * BASE by {
                cmm_divisible_lemma_2(key, S);
            }

            assert uh64(temp) as nat * key.R + sint(A') == sint(S[1..]) by {
                assert A' == A'[0..key.len] == S[1..key.len+1] by {
                    assert forall k :: 0 <= k < key.len ==> A'[k] == S[k + 1];
                }
                cmm_ghost_lemma(A', S, temp, key.len);
            }
        }

        assert uh64(temp) as nat * key.R + sint(A') < sint(y) + key.n_val
            && uh64(temp) <= 1 
            && (uh64(temp) == 1 ==> sint(A') < key.n_val)
        by {
            cmm_bounded_lemma_1(key, u_i, x_i, uh64(temp), y, A', A);
        }

        ghost var result := x_i as nat * sint(y) + u_i as nat * key.n_val + sint(A);

        if uh64(temp) != 0 {
            var b, A'' := seq_sub(A', key.m);
            calc == {
                result;
                {
                    assert uh64(temp) == 1;
                }
                (key.R + sint(A')) * BASE;
                {
                    assert sint(A') + key.R == sint(A'') + key.n_val;
                }
                (sint(A'') + key.n_val) * BASE;
            }
            
            assert cong((sint(A'') + key.n_val) * BASE, result, key.n_val) by {
                reveal cong();
            }

            calc ==> {
                cong((sint(A'') + key.n_val) * BASE, result, key.n_val);
                {
                    mod_mul_lemma(-BASE, key.n_val, key.n_val);
                    cong_add_lemma_3((sint(A'') + key.n_val) * BASE, -key.n_val * BASE,  key.n_val);
                    reveal cong();
                }
                cong((sint(A'') + key.n_val) * BASE - key.n_val * BASE, result, key.n_val);
                {
                    assert (sint(A'') + key.n_val) * BASE - key.n_val * BASE == sint(A'') * BASE;
                }
                cong(sint(A'') * BASE, result, key.n_val);
            }

            assert cong(sint(A'') * BASE, result, key.n_val);

            A' := A'';
        } else {
            assert sint(A') < sint(y) + key.n_val;
            assert cong(sint(A') * BASE, result, key.n_val) by {
                assert sint(A') * BASE == result;
                reveal cong();
            }
        }

        assert cong(sint(A'), sint(x[..i+1]) * sint(y) * power(key.BASE_INV, i+1), key.n_val) by {
            cmm_congruent_lemma(key, x, i, x_i as nat, u_i as nat, sint(A), sint(A'), sint(y));
        }
    }

    method montMul(key: pub_key, x: seq<uint32>, y: seq<uint32>)
        returns (A: seq<uint32>)

        requires pub_key_valid(key);
        requires |x| == |y| == key.len;

        ensures cong(sint(A), sint(x) * sint(y) * key.R_INV, key.n_val);
        ensures sint(A) < key.n_val + sint(y);
        ensures |A| == key.len;
    {
        A  := zero_seq_int(key.len);
        assert sint(A) == 0;

        ghost var y_val := sint(y);

        var i := 0;

        assert cong(sint(A), sint(x[..i]) * sint(y) * power(key.BASE_INV, i), key.n_val) by {
            assert sint(A) == sint(x[..i]) * sint(y) * power(key.BASE_INV, i);
            reveal cong();
        }
        
        while i != key.len
            decreases key.len - i;
            invariant i <= |x|;
            invariant |A| == key.len;

            invariant cong(sint(A), sint(x[..i]) * sint(y) * power(key.BASE_INV, i), key.n_val);
            invariant sint(A) < key.n_val + sint(y);
        {
            A := montMulAdd(key, A, x[i], y, i, x);
            i := i + 1;
        }

        assert cong(sint(A), sint(x) * sint(y) * power(key.BASE_INV, i), key.n_val) by {
            assert x == x[..key.len];
        }

        assert cong(sint(A), sint(x) * sint(y) * key.R_INV, key.n_val);
    }

    method modpow3(key: pub_key, a: seq<uint32>) 
        returns (aaa: seq<uint32>)

        requires pub_key_valid(key);
        requires 0 <= sint(a) < key.n_val; 
        requires |a| == key.len;
        ensures sint(aaa) == power(sint(a), 3) % key.n_val;
        ensures |aaa| == key.len;
    {
        var aR := montMul(key, a, key.RR); /* aR = a * RR / R mod M   */
        var aaR := montMul(key, aR, aR); /* aaR = aR * aR / R mod M */
        aaa := montMul(key, aaR, a); /* aaa = aaR * a / R mod M */

        ghost var aaa_val := sint(aaa);
        ghost var a_val := sint(a);

        mod_pow3_congruent_lemma(key, a_val, sint(aR), sint(aaR), aaa_val, sint(key.RR));

        var geq := seq_geq(aaa, key.m);

        if geq {
            var _, temp := seq_sub(aaa, key.m);
            ghost var temp_val := sint(temp);
            
            assert cong(aaa_val, temp_val, key.n_val) by {
                assert temp_val == aaa_val - key.n_val;
                cong_add_lemma_3(aaa_val, - key.n_val, key.n_val);
            }
            cong_trans_lemma(temp_val, aaa_val, a_val * a_val * a_val, key.n_val);

            aaa := temp;
        }

        assert sint(aaa) == (a_val * a_val * a_val) % key.n_val by {
            assert 0 <= sint(aaa) < key.n_val;
            assert cong(sint(aaa), a_val * a_val * a_val, key.n_val);
            cong_remainder_lemma(sint(aaa), a_val * a_val * a_val, key.n_val);
        }

        assert (a_val * a_val * a_val == power(a_val, 3)) by {
            reveal power();
        }
    }

    method RSA_e_3_verify(key: pub_key, signature: seq<uint32>, sha: seq<uint32>, ghost rsa: rsa_params)
        returns (x : bool)

        requires pub_key_connect_valid(rsa, key);
        requires |signature| == |sha| == key.len;
        requires 0 <= sint(signature) < key.n_val;
        requires 0 <= sint(sha) < key.n_val;

        ensures x <==> sint(signature) == power(sint(sha), rsa.d) % key.n_val;
    {
        var buf := modpow3(key, signature);
        var i := 0;

        ghost var s := sint(signature);
        ghost var m := sint(sha);

        while i < key.len
            decreases key.len - i;
            invariant 0 <= i <= key.len;
            invariant buf[..i] == sha[..i];
        {
            if buf[i] != sha[i] {
                assert (s != power(m, rsa.d) % rsa.n) by {
                    assert sint(buf) != m by {
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