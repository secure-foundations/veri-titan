
# Verifying [OpenTitan](https://opentitan.org/)

## Signature Validation:

[C implementation](https://android.googlesource.com/platform/system/core.git/+/android-4.2.2_r1/libmincrypt/rsa_e_3.c) (from libmincrypt)

[Decrypto implementation](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c)


## Proof Triaging:

### Congruence Proofs: 
[cmm_divisible_lemma_1](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L49) 

This lemma, along with two aux lemmas (~100 lines) can be dispatched. 

[cmm_congruent_lemma](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/MMLemmas.dfy#L461)

This lemma, with some aux lemmas (~250 lines) can be dispatched.

[mod_pow3_congruent_lemma](https://github.com/secure-foundations/veri-titan/blob/8b219fe6228ca42f3c0ce4bb99cd865c73541ae0/dfy_model/RSALemmas.dfy#L100)

This lemma, with some aux lemmas (~100 lines) can be dispatched.

