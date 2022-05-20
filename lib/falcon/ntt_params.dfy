include "pows_of_2.dfy"

module ntt_params {
	import opened Power
	import opened Power2
	import opened DivMod
	import opened Mul

    import opened pows_of_2

	const Q: nat := 12289

	type elem = i :nat | i < Q

	ghost const N: pow2_t;
	ghost const PSI: elem;
	ghost const PSI_INV: elem;
	ghost const OMEGA: elem;
	ghost const OMEGA_INV: elem;
	ghost const R: elem;
	ghost const R2: elem;
	ghost const R_INV: elem;
	ghost const N_INV: elem;

	lemma {:axiom} Nth_root_lemma()
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