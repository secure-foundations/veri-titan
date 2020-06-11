include "NativeTypes.dfy"
include "SeqInt.dfy"
include "Powers.dfy"
include "Congruences.dfy"

module RSALemmas
{
    import opened Congruences
    import opened SeqInt
    import opened Powers
    import opened NativeTypes

    predicate {:opaque} coprime(a: nat, b: nat)
    predicate {:opaque} prime(a: nat)
    	ensures a >= 3;

    lemma cong_k_exist_lemma(a: int, b: int, n: int)
        requires n != 0;
    	requires cong(a, b, n);
    	ensures exists k :int :: a - b == n * k;

	lemma power_power_lemma(b: int, e1: nat, e2: nat)
        ensures power(power(b, e1), e2) == power(b, e1 * e2);

    lemma power_mod_lemma_2(b: int, e: nat, n: int)
        requires n != 0;
        ensures power(b % n, e) % n == power(b, e) % n;

    lemma fermats_little_theorem(a: int, p: nat)
    	requires prime(p) && !cong(a, 0, p);
    	ensures cong(power(a, p - 1), 1, p);

    lemma chinese_remainder_theorem(a: int, b: int, p: nat, q: nat)
        requires prime(p) && prime(q);
        requires cong(a, b, p) ;
        requires cong(a, b, q);
        ensures  cong(a, b, p * q);

    datatype pub_key = pub_key(
        e: nat, 
        m: seq<uint32>,
        RR: seq<uint32>,
        m': uint32,
        len: nat,
        n_val: int,
        BASE_INV: nat,
        R: nat,
        R_INV: nat
    )

    predicate pub_key_valid(key: pub_key) {
        && key.e == 3
        && |key.m| == |key.RR| == key.len >= 1
        && seq_interp(key.m) == key.n_val
        && 0 != key.n_val < power(BASE, key.len)
        && cong(key.m' as nat * key.m[0] as nat, -1, BASE)
        && cong(BASE * key.BASE_INV, 1, key.n_val)
        && key.R == power(BASE, key.len)
        && key.R_INV == power(key.BASE_INV, key.len)
        && cong(key.R_INV * key.R, 1, key.n_val)
        && 0 <= seq_interp(key.RR) < key.n_val
        && cong(seq_interp(key.RR), key.R * key.R, key.n_val)
    }

    datatype rsa_params = rsa_params(
        e: nat,
        d: nat,
        p: nat,
        q: nat,
        phi: nat,
        n: nat)

    predicate rsa_valid(rsa: rsa_params) 
    {
        && prime(rsa.p)
        && prime(rsa.q)
        && rsa.p * rsa.q == rsa.n
        && rsa.phi == (rsa.q - 1) * (rsa.p - 1)
        && coprime(rsa.phi, rsa.e)
        && 0 < rsa.d < rsa.phi
        && 0 < rsa.e < rsa.phi
        && cong(rsa.e * rsa.d, 1, rsa.phi)
    }

    predicate pub_key_connect_valid(rsa: rsa_params, key: pub_key)
    {
        && rsa_valid(rsa)
        && pub_key_valid(key)
        && rsa.e == key.e
        && rsa.n == key.n_val
    }

    lemma rsa_cong_lemma_1(rsa: rsa_params, m: nat, p: nat)
        requires rsa_valid(rsa);
        requires p == rsa.p || p == rsa.q;
        ensures cong(power(m, rsa.d * rsa.e), m, p);
    {
        var e, d := rsa.e, rsa.d;
        var q := if p == rsa.q then rsa.p else rsa.q;
        var n, phi := rsa.n, rsa.phi;

        if cong(m, 0, p) {
            rsa_cong_lemma_2(rsa, m, p);
        }  else {
            assert exists k :int :: (d * e == phi * k + 1) by {
                assert cong(d * e, 1, phi);
                cong_k_exist_lemma(d * e, 1, phi);
            }

            var k :| d * e == phi * k + 1;
            rsa_cong_lemma_3(rsa, m, p, k);
        }
    }

    lemma rsa_cong_lemma_2(rsa: rsa_params, m: nat, p: nat)
        requires rsa_valid(rsa);
        requires p == rsa.p || p == rsa.q;
        requires cong(m, 0, p);
        ensures cong(power(m, rsa.d * rsa.e), m, p);        
    {
        var d := rsa.d;
        var e := rsa.e;

        ghost var temp := power(m, d * e);
        assert cong(m, 0, p);

        calc ==> {
            cong(m, 0, p);
            {
                cong_power_lemma(m, 0, d * e, p);
            }
            cong(temp, power(0, d * e), p);
            cong(temp, 0, p);
            {
                assert cong(m, 0, p);
                cong_trans_lemma(temp, 0, m, p);
            }
            cong(temp, m, p);
        }
        assert cong(power(m, d * e), m, p);
    }

    lemma rsa_cong_lemma_3(rsa: rsa_params, m: nat, p: nat, k: int)
        requires rsa_valid(rsa);
        requires rsa.d * rsa.e == rsa.phi * k + 1;
        requires p == rsa.p || p == rsa.q;
        requires !cong(m, 0, p);
        ensures cong(power(m, rsa.d * rsa.e), m, p);
    {
        var e, d := rsa.e, rsa.d;
        var q := if p == rsa.q then rsa.p else rsa.q;
        var n, phi := rsa.n, rsa.phi;

        assert cong_a1 : power(power(m, p - 1), (q - 1) * k) == power(m, phi * k) by {
            rsa_cong_lemma_4(rsa, m, p, q, k);
        }

        calc ==> {
            prime(p) && !cong(m, 0, p);
            {
                fermats_little_theorem(m, p);
            }
            cong(power(m, p - 1), 1, p); 
            {
                cong_power_lemma(power(m, p - 1), 1, (q - 1) * k, p);
            }
            cong(power(power(m, p - 1), (q - 1) * k), power(1, (q - 1) * k), p);
           {
                power_base_one_lemma((q - 1) * k);
            }
            cong(power(power(m, p - 1), (q - 1) * k), 1, p);
            {
                reveal cong_a1;
            }
            cong(power(m, phi * k), 1, p);
        }

        assert cong(power(m, phi * k), 1, p); // splitting here helps for some reason

        calc ==> {
            cong(power(m, phi * k), 1, p);
            {
                cong_mul_lemma_1(power(m, phi * k), 1, m, p);
            }
            cong(power(m, phi * k) * m, m, p);
            {
                power_add_one_lemma(m, phi * k);
            }
            cong(power(m, phi * k + 1), m, p);
            {
                assert d * e == phi * k + 1;
            }
            cong(power(m, d * e), m, p);
        }

        assert cong(power(m, d * e), m, p);
    }

    // unstable
    lemma rsa_cong_lemma_4(rsa: rsa_params, m: nat, p: nat, q: nat, k: int)
        requires rsa_valid(rsa);
        requires rsa.d * rsa.e == rsa.phi * k + 1;
        requires p == rsa.p || p == rsa.q;
        requires if p == rsa.q then q == rsa.p else q == rsa.q;
        ensures power(power(m, p - 1), (q - 1) * k) == power(m, rsa.phi * k);
    {
        var e, d := rsa.e, rsa.d;
        var n, phi := rsa.n, rsa.phi;

        assert power(power(m, p - 1), (q - 1) * k) == power(m, phi * k) by {
            calc == {
                power(power(m, p - 1), (q - 1) * k);
                {
                    power_power_lemma(m, p - 1, (q - 1) * k);
                }
                power(m, (p - 1) * (q - 1) * k);
                {
                    assert (p - 1) * (q - 1) == phi;
                }
                power(m, phi * k);
            }
        } 
    }

    lemma rsa_correct_lemma(rsa: rsa_params, m: nat)
        requires rsa_valid(rsa);
        requires m < rsa.n;
        ensures m == power(m, rsa.d * rsa.e) % rsa.n;
    {
        var e, d := rsa.e, rsa.d;
        var p, q := rsa.p, rsa.q;
        var n, phi := rsa.n, rsa.phi;

        assert cong(power(m, d * e), m, n) by {
            assert cong(power(m, d * e), m, p) by {
                rsa_cong_lemma_1(rsa, m, p);
            }
            assert cong(power(m, d * e), m, q) by {
                rsa_cong_lemma_1(rsa, m, q);
            }
            chinese_remainder_theorem(power(m, d * e), m, p, q);
        }

        assert m == power(m, d * e) % n by {
            assert cong(m, power(m, d * e), n) by {
                reveal cong();
            }
            cong_remainder_lemma(m, power(m, d * e), rsa.n);
        }
    }

    lemma rsa_signature_lemma(rsa: rsa_params, m: nat, s: nat)
        requires m < rsa.n && s < rsa.n;
        requires rsa_valid(rsa);
        ensures (power(s, rsa.e) % rsa.n == m) <==> (s == power(m, rsa.d) % rsa.n);
    {
        var e, d, n := rsa.e, rsa.d, rsa.n;

        if s == power(m, d) % n {
            calc == {
                power(s, e) % n;
                power(power(m, d) % n, e) % n;
                {
                    power_mod_lemma_2(power(m, d), e, n);
                }
                power(power(m, d), e) % n;
                {
                    power_power_lemma(m, d, e);
                }
                power(m, d * e) % n;
                {
                    assert m == power(m, d * e) % n by {
                       rsa_correct_lemma(rsa, m);
                    }
                }
                m;
            }
            assert power(s, e) % n == m;
        }

        if power(s, e) % n == m {
            calc == {
                power(m, d) % n;
                power(power(s, e) % n, d) % n;
                {
                    power_mod_lemma_2(power(s, e), d, n);
                }
                power(power(s, e), d) % n;
                {
                    power_power_lemma(s, e, d);
                }
                power(s, e * d) % n;
                {
                    assert s == power(s, d * e) % n by {
                       rsa_correct_lemma(rsa, s);
                    }
                }
                s;
            }
            assert s == power(m, d) % n;
        }
    }
}