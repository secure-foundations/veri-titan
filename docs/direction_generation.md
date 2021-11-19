# Proof Generation Proposal:
----

To provide high assurance, cryptographic libraries are often formally verified for correctness. In some cases the verification is done on the high level source code, then a compiler is entrusted to emit the correct assembly. Alternatively, the verification can also be performed on the assembly code directly, since hand-written assembly can often achieve more optimized performance. 

Writing proofs for assembly is far from trivial. (Insert explanations on why this is hard). Writing proofs for a high level model is easier in comparison, albeit still challenging. (Insert explanations on why this is easier). 

In this work we explore a new approach towards verifying assembly implementations. Given a high-level model that is verified and a assembly implementation that needs to be verified
, we attempt to automatically derive the proof of correctness for the latter based on the former. Of course the model and the implementation cannot be arbitrary. For our purpose, we require them to be "semantically close", which we will also explore. 

A proof is consisted of pre/post conditions, invariants and additional assertions that helps it to go through. All of these are made up of predicates, which are claims about various subjects. For our purpose, the subjects of the predicates are relatively simple, where they can be:
* fixed width integers
* array of fixed width integer representing big integer
* ghost values that don't exist in the actual program flow

We note that assembly code also operate around these subjects, except that the values and pointers are stored in registers instead of variables in the high-level model. If we are able to find the correspondence, then we should be able to substitute for the subjects in the existing model to generate a proof for the assembly. 

<!-- # Problem:
We are given:
* an algorithm `A`: an algorithm to be implemented
* a model `M`: some Dafny code that gives a high level model of the algorithm `A`
* a proof `P1`: some Dafny proof around `M`, certifying its correctness
* a implementation `I`: some assembly implementation of the algorithm `A`

We intend to generate:
* a proof `P2`: a (Vale/Dafny) proof for the correctness of `I`, based on `M` and `P1`

# Assumption:
The main assumption is that `M` semantically close to `I`, despite one being written in a high level language and the other in assembly.
* The subjects in `P1` should be relatively low level, matching the subjects in `P2`. If we are reasoning about mathematical integers in the `P1`, which simply do not fit into the registers in `P2`, it would be challenging to establish the connection.
* We need to systematically overcome other differences. For example loop predicates typically don't depend on the registers directly, instead operations are performed on the registers, flags are set, and the branching depends on the register. 

# Intuitions:
* `P1` is closely connected to `M` by nature, since the proof is written alongside with the model.
* If `M` is semantically close to `I`, then the predicates needed in `P2` should be similar to the ones we need in `P1`.
* The types of subjects are limited in theses predicates. We need to reason about arrays and fixed width integers. No fancy structures are involved.
* If we can automatically figure out what the equivalent subjects are, then we can plug in the subject from `I` into `P1`, generating `P2`.

# Proposed Workflow:
* pre-process`P1` alongside `M`. -->

# Related Works:

----
## [Get Rid of Inline Assembly through Verification-Oriented Lifting](https://rbonichon.github.io/papers/tina-ase19.pdf)

### Motivation:
Inline assembly code is often needed along side with C code. The problem is that inline assembly makes formal analysis on the code difficult. Say I have some tool that works on C, it will not be able to handle the inline assembly parts.

This paper describes an approach to "decompile" the inline assembly code into C code, in a way that is amenable towards formal analysis. 

### Insights:
Semantic persevering deompilation in general is hard. So they have to work off certain assumptions. They identify several properties of inline assembly:
* The control flow structure is limited: only a handful
of conditionals and loops, hosting up to hundreds of
instructions;
* The interface of the chunk with the C code is usually
given: programmers annotate chunks with the description
of its inputs, outputs and clobbers with respect to its C
context
* Furthermore, the chunk appears in a C context, where
the types, and possibly more, are known: they only need to propagate the information here.

### Overall Work Flow:
* Compilation: the source code is compiled with debugging symbols
* IR lifting: the binary is then lifted into a simple IR.
* C lifting: the IR is translated into C code
* Validation: the decompiled C code is validated. 

The last two steps are the meat of their work.

### IR -> C Part:
There are several difficulties are in the IR -> C step:

* Low-level data: explicit flags, including overflows or
carry, bitwise operations (masks), low-level comparisons they don't have good correspondence with C code.

    To address this issue, they refer to an external technique that can prove equivalence of low level predicates. So instead of control flow condition depending on a bit in the flag register, it will depend on expressions from registers.

* Implicit variables: separate logical variables could be packed inside a large register. like different parts of the same register corresponds to different C variables. 

    To address this, they used something called register unpacking. They basically split up register to 8/16/32 bit sizes. Then they see if any of them is being used and assign a variable to it. Unused ones are eliminated. 

    They also talk about expression propagation. From my understanding they are propagating symbolic values, aggregating them into expressions, then a simplification pass happens over the expressions. 

* Implicit loop counters/index: structures indexed by loop
counters at high-level are split into multiple low-level
computations where the link between the different logical
elements is lost.

    To address this they used a pass called loop normalization. Basically recovering the loop counter.

### Validation Part:

They compile the "decompiled" C code, and re-lift the compiled code. Then they demonstrate that the re-lifted code is equivalent to the IR derived from the inline assembly. 

The validation is done through something called block-based semantic equivalence. 
* isomorphism of the control-flow graphs extracted from the two lifted programs
* pairwise equivalence of corresponding vertices using SMT, or fall back with randomized testing.

### Comments:
* The validation process in this paper (Figure 4) is a bit circular. 
* This paper uses the term verification a lot, but it is more general formal analysis. The evaluation section seems a bit short. 
* It is a fair point that os/hardware specific instructions cannot be lifted/decompiled easily, since there is no correspondence with C.
----

## [HACLxN: Verified Generic SIMD Crypto](https://eprint.iacr.org/2020/572.pdf)

## [The Last Mile: High-Assurance and High-Speed Cryptographic Implementations](https://arxiv.org/pdf/1904.04606.pdf)

## [Simple High-Level Code For Cryptographic Arithmetic – With Proofs, Without Compromises](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf)


