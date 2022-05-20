include "pows_of_2.dfy"

abstract module ntt_params {
	import opened Power
	import opened DivMod
    import opened pows_of_2

	const Q: nat;
	ghost const N: pow2_t;
	ghost const PSI: elem;
	ghost const PSI_INV: elem;
	ghost const OMEGA: elem;
	ghost const OMEGA_INV: elem;
	ghost const R: elem;
	ghost const R2: elem;
	ghost const R_INV: elem;
	ghost const N_INV: elem;

	type elem = i :nat | i < Q witness *

	lemma Nth_root_lemma()
		ensures Q >= 1;
		ensures N.exp >= 2;
		ensures Pow(PSI, 2 * N.full) % Q == 1
		ensures Pow(PSI, N.full) % Q == Q - 1
		ensures (PSI * PSI_INV) % Q == 1

		ensures Pow(OMEGA, N.full) % Q == 1
		ensures Pow(OMEGA_INV, pow2_half(N).full) % Q == Q - 1
		ensures (OMEGA * OMEGA_INV) % Q == 1

		ensures (R_INV * R) % Q == 1
		ensures IsModEquivalent(R2, R * R, Q); 

		ensures (N_INV * N.full) % Q == 1;
}

module ntt_512_params refines ntt_params {
	import opened Power2

	function pow2_9(): pow2_t
	{
		Lemma2To64();
		pow2(9)
	}

    const Q := 12289

	ghost const N := pow2_9();

	lemma Nth_root_lemma()
	{
		assume Pow(PSI, 2 * N.full) % Q == 1;
		assume Pow(PSI, N.full) % Q == Q - 1;
		assume (PSI * PSI_INV) % Q == 1;

		assume Pow(OMEGA, N.full) % Q == 1;
		assume Pow(OMEGA_INV, pow2_half(N).full) % Q == Q - 1;
		assume (OMEGA * OMEGA_INV) % Q == 1;

		assume (R_INV * R) % Q == 1;
		assume IsModEquivalent(R2, R * R, Q); 

		assume (N_INV * N.full) % Q == 1;
	}
}