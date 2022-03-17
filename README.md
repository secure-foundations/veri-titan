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
The `arch` directory contains the code describing the machine models for OTBN and RISC-V. In particular, for each architecture:
1. A `machine.s.dfy` file describes the machine model, which describes the
   architecture's maintained machine state (registers, flags, and instruction
format). It also contains the executable semantics for the architecture.
2. A `decls.i.dfy` file describes the semantics for each instruction in the form of
   a Hoare triple. These definitions are untrusted, and implemented using the trusted operations defined in `machine.s.dfy`.
3. A 'vale.s.dfy' file that contains architecture-specific, user-defined types,
   functions, and lemmas which are used in generated Dafny files.

The `impl` directory contains the Vale implementations for the RSA signature
verification routines. The OTBN implementation is based off of the code
[here](https://github.com/lowRISC/opentitan/tree/master/sw/otbn/code-snippets)
and the RISC-V implementation is based off of the code
[here](https://github.com/secure-foundations/veri-titan/blob/master/temp/crypto_examples/rsa_verify/rv32imc/dump.asm).

Note that one central convention is that all trusted specification files end in `.s.dfy.` Everything else should be a `.i.dfy` file and will be verified for correctness.

<!--
## Signature Validation Implementations:

[C implementation](https://android.googlesource.com/platform/system/core.git/+/android-4.2.2_r1/libmincrypt/rsa_e_3.c)

[decrypto implementation](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c)

[decrypto spec](https://docs.google.com/document/d/1k953gdDgJFX4m2ij66Pojjz_Nk18F5vXXaknaFwJem4/)

[OTBN implementation](https://github.com/lowRISC/opentitan/tree/master/sw/otbn/code-snippets)

[OTBN spec](https://docs.opentitan.org/hw/ip/otbn/doc/)

 [Calling Convention](https://docs.google.com/document/d/1aXaWaXGvGPB9rdF4x1r6weH69l0ghYDevhTZqEtJ8DU) -->

## Build Instructions 

We assume the following packages are installed by the user:

`ninja` (1.10.+)

[`dotnet`](https://dotnet.microsoft.com/download)

[`nuget`](https://www.nuget.org/downloads)

[`python`](https://www.python.org/) >= 3.0

We also assume some otbn tools are available:

[`otbn-as`](https://github.com/lowRISC/opentitan/tree/master/hw/ip/otbn/util)

[`otbn-ld`](https://github.com/lowRISC/opentitan/tree/master/hw/ip/otbn/util)

Finally, you will need all the Vale dependencies listed
[here](https://github.com/project-everest/vale/blob/otbn-custom/INSTALL.md#building-vale-from-source).
This is because a custom version of Vale will be compiled from source during
setup.

To prepare for the build process, run: 
```
python3 build.py setup
```
The setup will install custom versions of `dafny` and `vale`, and download a version of Dafny standard library. The setup should only need to be ran once. 

We rely on `ninja` for building the project. To generate a `build.ninja` file for this project, run:
```
python3 build.py
```
Then run: 
```
ninja -v -j4
```
This will start the build using 4 threads. The build output are all in the `gen` directory. `gen/arch/otbn/printer.s.dll.out` contains the printer output assembly code form the project. `gen/impl/otbn/run_modexp.elf` is currently the linked `elf` file assembled from the printer output. 
 
## Research Potentials:

Making Assembly Proofs Easier

1. [proof generation](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_generation.md)
2. [width independent proofs](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_width.md)
3. [algebra solvers](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_algebra.md)

Building a Verified Hardware Root of Trust

[Closing the Hardware/Software Gap](https://github.com/secure-foundations/veri-titan/blob/master/documents/direction_hardware.md)
