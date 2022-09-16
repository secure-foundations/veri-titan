include "pow2.s.dfy"

abstract module ntt_param_s {
    import opened Power
    import opened DivMod
    import opened pow2_s

    type modulus = i: nat | 
        i % 2 == 1 && i > 1 witness 3

    const Q: modulus;

    predicate is_elem(i: nat)
        ensures is_elem(i) ==> (i % Q == i)
    {
        assert i < Q ==> (i % Q == i) by {
            if i < Q {
                LemmaSmallMod(i, Q);
            }
        }
        i < Q
    }

    type elem = i: nat | is_elem(i)

    const PSI: elem;
    const PSI_INV: elem;
    const OMEGA: elem;
    const OMEGA_INV: elem;
    const R: elem;
    const R2: elem;
    const R_INV: elem;
    const N_INV: elem;

    const N: pow2_t;

    type elems = s: seq<elem>
        | |s| == N.full witness *

    lemma Nth_root_lemma()
        ensures N.exp >= 2;

        ensures IsModEquivalent(Pow(PSI, 2), OMEGA, Q);
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