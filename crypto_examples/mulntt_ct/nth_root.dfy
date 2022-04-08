include "../ntt_cleanup/pow2.dfy"

module omegas {
	import opened Power
	import opened Power2
	import opened DivMod
	import opened Mul
	import opened pows_of_2

	const Q: nat := 12289
	
	type elem = i :nat | i < Q

	const PSI: nat := 7 // 2048-th root of unity
	const OMEGA: nat := 8209 // 1024-th root of unity

	const N: nat := 1024
	const DN: nat := 2 * N
	const LOGN: nat := 10
	const LOGDN: nat := 11

	lemma {:axiom} Nth_root_lemma()
		ensures Pow(PSI, Pow2(LOGDN)) % Q == 1;
		ensures Pow2(LOGDN) == DN;
		ensures Pow(PSI, Pow2(LOGN)) % Q == Q - 1;
		ensures Pow(OMEGA, Pow2(LOGN)) % Q == 1;
		ensures Pow2(LOGN) == N;

	function method omega(n: pow2_t): (v: elem)
		requires n.exp <=LOGDN;
		ensures Pow(v, n.full) % Q == 1;
	{
		var omg := Pow(PSI, Pow2(LOGDN - n.exp)) % Q;
		assert Pow(omg, n.full) % Q == 1 by {
			calc == {
				Pow(Pow(PSI, Pow2(LOGDN - n.exp)) % Q, n.full) % Q;
				{
					LemmaPowModNoop(Pow(PSI, Pow2(LOGDN - n.exp)), n.full, Q);
				}
				Pow(Pow(PSI, Pow2(LOGDN - n.exp)), n.full) % Q;
				{
					LemmaPowMultiplies(PSI, Pow2(LOGDN - n.exp), n.full);
				}
				Pow(PSI, Pow2(LOGDN - n.exp) * n.full) % Q;
				Pow(PSI, Pow2(LOGDN - n.exp) * Pow2(n.exp)) % Q;
				{
					reveal Pow2();
					LemmaPowAdds(2, LOGDN - n.exp, n.exp);
				}
				Pow(PSI, Pow2(LOGDN)) % Q;
				{
					Nth_root_lemma();
				}
				1;
			}
		}
		omg
	}

	function method omega_k(n: pow2_t, k: nat): elem
		requires n.exp <= LOGDN;
	{
		Pow(omega(n), k) % Q
	}

	lemma ntt_cancellation_lemma(n: pow2_t, k: nat)
		requires n.exp != 0;
		requires n.exp <= LOGDN;
		ensures omega_k(pow2_half(n), k) == omega_k(n, 2 * k);
	{
	  	calc {
			omega_k(pow2_half(n), k);
			Pow(omega(pow2_half(n)), k) % Q;
			Pow(Pow(PSI, Pow2(LOGDN - pow2_half(n).exp)) % Q, k) % Q;
			Pow(Pow(PSI, Pow2(LOGDN - (n.exp - 1))) % Q, k) % Q;
			Pow(Pow(PSI, Pow2(LOGDN - n.exp + 1)) % Q, k) % Q;
			{ LemmaPowModNoop(Pow(PSI, Pow2(LOGDN - n.exp + 1)), k, Q); }
			Pow(Pow(PSI, Pow2(LOGDN - n.exp + 1)), k) % Q;
			calc {
				Pow2(LOGDN - n.exp + 1);
				{ reveal Pow2(); reveal Pow(); }
				2*Pow2(LOGDN - n.exp);
			}
			Pow(Pow(PSI, Pow2(LOGDN - n.exp)*2), k) % Q;
			{ LemmaPowMultiplies(PSI, Pow2(LOGDN - n.exp), 2); }
			Pow(Pow(Pow(PSI, Pow2(LOGDN - n.exp)), 2), k) % Q;
			{ LemmaPowMultiplies(Pow(PSI, Pow2(LOGDN - n.exp)), 2, k); } 
			Pow(Pow(PSI, Pow2(LOGDN - n.exp)), 2*k) % Q;
			{ LemmaPowModNoop(Pow(PSI, Pow2(LOGDN - n.exp)), 2*k, Q); }
			Pow(Pow(PSI, Pow2(LOGDN - n.exp)) % Q, 2*k) % Q;
			Pow(omega(n), 2*k) % Q;
			omega_k(n, 2 * k);
		}
	}

	function method modpow(a: elem, b: nat): elem
	{
		Pow(a, b) % Q
	}

	function method modmul(a: elem, b: elem): elem
	{
		(a * b) % Q
	}

	function method modadd(a: elem, b: elem): elem
	{
		(a + b) % Q
	}

	function method modsub(a: elem, b: elem): elem
	{
		(a - b) % Q
	}

	lemma omega_k_mul_lemma(n: pow2_t, k1: nat, k2: nat)
		requires n.exp <= LOGDN;
		ensures 
			modmul(omega_k(n, k1), omega_k(n, k2))
				==
			omega_k(n, k1 + k2);
	{
		calc == {
			modmul(omega_k(n, k1), omega_k(n, k2));
			((Pow(omega(n), k1) % Q) * (Pow(omega(n), k2) % Q)) % Q;
			{
			   LemmaMulModNoopGeneral(Pow(omega(n), k1), Pow(omega(n), k2), Q);
			}
			(Pow(omega(n), k1) * Pow(omega(n), k2)) % Q;
			{
				LemmaPowAdds(omega(n), k1, k2);
			}
			Pow(omega(n), k1 + k2) % Q;
		}
	}

	lemma omega_k_square(n: pow2_t, k: nat)
		requires n.exp <= LOGDN;
		ensures 
			modmul(omega_k(n, k), omega_k(n, k))
				==
			omega_k(n, 2 * k);
	{
		omega_k_mul_lemma(n, k, k);
	}

	lemma ntt_zero_lemma(n: pow2_t)
		requires n.exp <= LOGDN;
		ensures omega_k(n, n.full) == 1;
		decreases n.exp;
	{
		pow2_basics(n);

		if n.exp == 0 {
			calc {
				omega_k(n, n.full);
				omega_k(n, 1);
				{
					LemmaPow1Auto();
				}
				omega(n) % Q;
				(Pow(PSI, Pow2(LOGDN - n.exp)) % Q) %Q;
				{
					LemmaModBasicsAuto();
				}
				Pow(PSI, Pow2(LOGDN - n.exp)) % Q;
				Pow(PSI, Pow2(LOGDN)) % Q;
				{
					Nth_root_lemma();
				}
				1;
			}
			return;
		}
	
		var n' := pow2_half(n);

		assert n'.full == n.full / 2;

		calc {
			omega_k(n, n.full);
			{
				ntt_cancellation_lemma(n, n'.full);
			}
			omega_k(n', n'.full);
			{
				ntt_zero_lemma(n');
			}
			1;
		}
	}

	lemma ntt_neg_one_lemma(n: pow2_t)
		requires 1 <= n.exp <= LOGDN;
		requires n.full % 2 == 0;
		ensures omega_k(n, n.full / 2) == Q - 1;
		decreases n.exp
	{
		if n.exp == 1 {
			pow2_basics(n);
			assert n.full == 2;
			calc == {
				omega_k(n, 1);
				Pow(omega(n), 1) % Q;
				{
					LemmaPow1(omega(n)); 
				}
				omega(n) % Q;
				(Pow(PSI, Pow2(LOGDN - n.exp)) % Q) % Q;
				{
					LemmaModBasicsAuto();
				}
				Pow(PSI, Pow2(LOGDN - 1)) % Q;
				Pow(PSI, Pow2(10)) % Q;
				{
					assert Pow2(LOGN) == N by {  Lemma2To64(); }
				}
				Pow(PSI, N) % Q;
				{
					Lemma2To64();
					assert N == pow2(LOGN).full;
					Nth_root_lemma();
				}
				Q - 1;
			}
			return;
		}

		var k := n.full / 2;
		var n' := pow2_half(n);

		pow2_basics(n');
		
		calc == {
			omega_k(n, k);
			{
				ntt_cancellation_lemma(n, n'.full / 2);
			}
			omega_k(n', n'.full / 2);   
			{
				ntt_neg_one_lemma(n');
			}
			Q-1;
		}
	}

	lemma ntt_halving_lemma(n: pow2_t, k: nat)
		requires 1 <= n.exp <= LOGDN
		ensures omega_k(n, 2 * k + n.full)
				==
			omega_k(n, 2 * k);
	{
		var x0 := omega_k(n, k + n.full / 2);
		var xx0 := modmul(x0, x0);

		var x1 := omega_k(n, k);
		var xx1 := modmul(x1, x1);

		pow2_basics(n);

		omega_k_square(n, k + n.full / 2);
		assert xx0 == omega_k(n, 2 * k + n.full);

		omega_k_square(n, k);
		assert xx1 == omega_k(n, 2 * k);

		calc == {
			omega_k(n, 2 * k + n.full);
			{
				omega_k_mul_lemma(n, 2 * k, n.full);
			}
			modmul(omega_k(n, 2 * k), omega_k(n, n.full));
			{
				ntt_zero_lemma(n);
			}
			omega_k(n, 2 * k) % Q;
			{
				LemmaModBasicsAuto();
			}
			omega_k(n, 2 * k);
		}
	}

	lemma omega_k_canonical(n: pow2_t, k: nat)
		requires n.exp <= LOGDN
		ensures Pow2(LOGDN - n.exp) * k >= 0;   
		ensures omega_k(n, k) == Pow(PSI, Pow2(LOGDN - n.exp) * k) % Q;
	{
		var om_nk := omega_k(n, k);
		var temp := Pow(PSI, Pow2(LOGDN - n.exp));
		LemmaPowPositiveAuto();

		calc == {
			om_nk;
			Pow(omega(n), k) % Q;
			Pow(temp % Q, k) % Q;
			{
				LemmaPowModNoop(temp, k, Q);
			}
			Pow(temp, k) % Q;
			Pow(Pow(PSI, Pow2(LOGDN - n.exp)), k) % Q;
			{
				LemmaPowMultiplies(PSI, Pow2(LOGDN - n.exp), k);
			}
			Pow(PSI, Pow2(LOGDN - n.exp) * k) % Q;
		}

		assert Pow2(LOGDN - n.exp) * k >= 0 by {
			LemmaMulStrictlyPositiveAuto();
		}
	}
}
