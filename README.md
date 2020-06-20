
# Verifying [OpenTitan](https://opentitan.org/)

## Signature Validation:

[C implementation](https://android.googlesource.com/platform/system/core.git/+/android-4.2.2_r1/libmincrypt/rsa_e_3.c) (from libmincrypt)

[Decrypto implementation](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c)


## Proof Triaging:
----
### Congruence Proofs: 

There are some lemma that are about proving congruences, which can be automated using Grobner bases method. 

[cmm_divisible_lemma_1](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L49) 

[cmm_congruent_lemma](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L461)

[mod_pow3_congruent_lemma](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/RSALemmas.dfy#L100)

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
* The proofs themselves are quite intuitive, just some basic properties about the big int in general.
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