
# Verifying [OpenTitan](https://opentitan.org/)

## Signature Validation Implementations:

[C implementation](https://android.googlesource.com/platform/system/core.git/+/android-4.2.2_r1/libmincrypt/rsa_e_3.c)

[decrypto implementation](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c)

[decrypto spec](https://docs.google.com/document/d/1k953gdDgJFX4m2ij66Pojjz_Nk18F5vXXaknaFwJem4/)

[OTBN implementation](https://github.com/lowRISC/opentitan/tree/master/sw/otbn/code-snippets)

[OTBN spec](https://docs.opentitan.org/hw/ip/otbn/doc/)

[Calling Convention](https://docs.google.com/document/d/1aXaWaXGvGPB9rdF4x1r6weH69l0ghYDevhTZqEtJ8DU)

## Research Potentials:

Making Assembly Proofs Easier

1. [proof generation](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_generation.md)
2. [width independent proofs](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_width.md)
3. [algebra solvers](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_algebra.md)

Building a Verified Hardware Root of Trust

[Closing the Hardware/Software Gap](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_hardware.md)

