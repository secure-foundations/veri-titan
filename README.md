
# Verifying [OpenTitan](https://opentitan.org/)

## Signature Validation:

[C implementation](https://android.googlesource.com/platform/system/core.git/+/android-4.2.2_r1/libmincrypt/rsa_e_3.c) (from libmincrypt)

[Decrypto implementation](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c)


## Proof Triaging:
----
### Congruence Proofs: 

There are some lemma that are about proving congruences, which can be automated using Grobner bases method via Singular. 

[cmm_divisible_lemma_1](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L49) 

```
ring r=integer,(m', m_0, k_1, p_1, x_i, y_0, a_0, p_1_lh, k_2, u_i, k_3, p_2, BASE),lp;
ideal I = m' * m_0 + 1 - k_1 * BASE,
    p_1 - x_i * y_0 - a_0,
    p_1_lh - p_1 - k_2 * BASE,
    u_i - p_1 * m' - k_3 * BASE,
    p_2 - u_i * m_0 - p_1_lh,
    BASE;
ideal G = groebner(I);
reduce(p_2, G);
```

[cmm_congruent_lemma](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L461)

```
ring r=integer,(BASE, BASE_INV, BASE_pow_i, BASE_INV_pow_i, n, A, x, y, A', x_i, x', k_1, k_2, k_3, k_4),lp;
ideal I = BASE * BASE_INV - 1 - k_1 * n,
	BASE_pow_i * BASE_INV_pow_i - 1 - k_2 * n,
	A - x * y * BASE_INV_pow_i - k_3 * n,
	A' * BASE - x_i * y - A - k_4 * n,
	x' - x - BASE_pow_i * x_i,
	n;
ideal G = groebner(I);
reduce(A' - x' * y * BASE_INV_pow_i * BASE_INV, G);
```

[mod_pow3_congruent_lemma](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/RSALemmas.dfy#L100)

```
ring r=integer,(R, R_INV, rr, ar, a, aar, aaa, k_1, k_2, k_3, k_4, k_5, n),lp;
ideal I = R * R_INV - 1 - k_1 * n,
    rr - R * R - k_2 * n,
    ar - a * rr * R_INV - k_3 * n,
    aar - ar * ar * R_INV - k_4 * n,
    aaa - aar * a * R_INV - k_5 * n,
    n;
ideal G = groebner(I);
reduce(aaa - a * a * a, G);
```

----
### Equational Proofs: 

There are a few lemmas where we need to show some equality, given some equalities.
* Dafny is actually quite good at equational reasoning, even with non-linear math (surprisingly), which is at the core of these lemmas.
* Things gets complicated by recursive definitions that need to unfolded the right way, which Dafny can't effectively do. But the definitions only need to be unfolded constant number of times (1 in most cases). (Maybe setting the right fuel could already help here.)
* Grobner bases method also applies to equational reasoning, but does not help with the recursive definition unfolding.

[cmm_invarint_lemma_1](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L171)

[cmm_invarint_lemma_2](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L197)

[cmm_invarint_lemma_3](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L356)

----
### Big Int Induction Proofs: 

There are a few cases where we need to induct on the big integer
* The proofs themselves are quite intuitive (trivial), just some basic properties about the big ints in general.
* Proofs pretty much follow the same pattern, with induction on the sequence length. Recursive definitions needs to have controlled unfolding.

[neq_aux_lemma_2](https://github.com/secure-foundations/veri-titan/blob/2fd39315020e3c094b0cc1c1a0ccd315803128cb/dfy_model/SeqInt.dfy#L239)

[seq_div_base_lemma](https://github.com/secure-foundations/veri-titan/blob/2fd39315020e3c094b0cc1c1a0ccd315803128cb/dfy_model/SeqInt.dfy#L864)

----
### Power() Proofs: 

Reasoning around `Power()` is a bit awkward.
* lemmas related to `Power()` needs to be proved
* these lemmas then need to be invoked explicitly

[this file](https://github.com/secure-foundations/veri-titan/blob/dafny-model-dev/dfy_model/Powers.dfy) is all about proving some trivial lemmas about `Power()`. 

[this calc](https://github.com/secure-foundations/veri-titan/blob/2fd39315020e3c094b0cc1c1a0ccd315803128cb/dfy_model/RSALemmas.dfy#L280) is an example where the lemmas are being invoked. 