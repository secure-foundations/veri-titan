# Verifying [OpenTitan](https://opentitan.org/)
OpenTitan is an open source silicon Root of Trust (RoT) project, which includes
a firmware design and implementation of a secure boot process. This repository
contains two experimental verified implementations of an RSA signature
verification routine used in the OpenTitan Mask ROM, one in RISC-V and the
other in the [OpenTitan Big Number
Accelerator](https://docs.opentitan.org/hw/ip/otbn/doc/) (OTBN) ISA for
OpenTitan's cryptographic hardware accelerator.

We are motivated by the following observation: formal proofs are often employed
to show correctness of cryptographic routines at the assembly level, and while
the same cryptographic routines are often implemented on different ISAs, the
current cost of verification effort scales poorly with the number of
architectures. This project aims to learn, through verifying two
implementations of the same procedure in two different architectures, how to
automate the process of proving the same routine for future architectures.

## Verified Implemenations in Vale
Our verified implementations are slightly adapted from the current machine code
implementations from the OpenTitan project, in instances where instruction
reordering simplified verification but did not semantically alter the code.

The implementations are verified using a customized development of the
[Dafny](https://github.com/dafny-lang/dafny) variant of
[Vale](https://github.com/project-everest/vale/tree/otbn-custom), which is
described in:
> [Vale: Verifying High-Performance Cryptographic Assembly Code](https://project-everest.github.io/assets/vale2017.pdf)  
> Barry Bond, Chris Hawblitzel, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch, Bryan Parno, Ashay Rane, Srinath Setty, Laure Thompson.  
> In Proceedings of the USENIX Security Symposium, 2017.  
> Distinguished Paper Award

The `otbn-custom` branch builds directly on top of the `dafny-legacy` branch,
and exposes additional Dafny language features within Vale procedures.

## Repository Organization
The `arch` directory contains the trusted code describing the machine models for OTBN and RISC-V. In particular, for each architecture:
1. A `machine.s.dfy` file describes the machine model, which describes the
   architecture's maintained machine state (registers, flags, and instruction
format).
2. A `decls.s.dfy` file describes the semantics for each instruction in the form of
   a Hoare triple.
3. A 'vale.s.dfy' file that contains architecture-specific, user-defined types,
   functions, and lemmas which are used in generated Dafny files.

The `impl` directory contains the Vale implementations for the RSA signature
verification routines. The OTBN implementation is based off of the code
[here](https://github.com/lowRISC/opentitan/tree/master/sw/otbn/code-snippets)
and the RISC-V implementation is based off of the code
[here](https://github.com/secure-foundations/veri-titan/blob/master/temp/crypto_examples/rsa_verify/rv32imc/dump.asm).


## Signature Validation Implementations:

[C implementation](https://android.googlesource.com/platform/system/core.git/+/android-4.2.2_r1/libmincrypt/rsa_e_3.c)

[decrypto implementation](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c)

[decrypto spec](https://docs.google.com/document/d/1k953gdDgJFX4m2ij66Pojjz_Nk18F5vXXaknaFwJem4/)

[OTBN implementation](https://github.com/lowRISC/opentitan/tree/master/sw/otbn/code-snippets)

[OTBN spec](https://docs.opentitan.org/hw/ip/otbn/doc/)

<!-- [Calling Convention](https://docs.google.com/document/d/1aXaWaXGvGPB9rdF4x1r6weH69l0ghYDevhTZqEtJ8DU) -->

## Dependecies

We assume the following packages are installed:

`ninja` (1.10.+)

[`dotnet`](https://dotnet.microsoft.com/download) 

[`nuget`](https://www.nuget.org/downloads)

We also assume some otbn tools are available:

[`otbn-as`](https://github.com/lowRISC/opentitan/tree/master/hw/ip/otbn/util)

[`otbn-ld`](https://github.com/lowRISC/opentitan/tree/master/hw/ip/otbn/util)

The setup script will install:

`dafny`

`vale`

## Research Potentials:

Making Assembly Proofs Easier

1. [proof generation](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_generation.md)
2. [width independent proofs](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_width.md)
3. [algebra solvers](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_algebra.md)

Building a Verified Hardware Root of Trust

[Closing the Hardware/Software Gap](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_hardware.md)
