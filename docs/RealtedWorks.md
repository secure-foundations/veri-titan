# Related Works:
----

## Get rid of inline assembly through verification-oriented lifting
----
Inline assembly code is often needed along side with C code. The problem is that inline assembly makes formal analysis on the code difficult. Say I have some tool that works on C, it will not be able to handle the inline assembly parts.

This paper describes an approach to "decompile" the inline assembly code into C code, in a way that is amenable towards formal analysis. 

Semantic persevere deompilation in general is hard. So they have to work off certain assumptions. They identify several properties of inline assembly:
* The control flow structure is limited: only a handful
of conditionals and loops, hosting up to hundreds of
instructions;
* The interface of the chunk with the C code is usually
given: programmers annotate chunks with the description
of its inputs, outputs and clobbers with respect to its C
context
* Furthermore, the chunk appears in a C context, where
the types, and possibly more, are known: they only need to propagate the information here.

Overall Work Flow:
* Compilation: the source code is compiled with debugging symbols
* IR lifting: the binary 
* C lifting
* Validation

Difficulties:
* Low-level data: explicit flags, including overflows or
carry, bitwise operations (masks), low-level comparisons they don't have good correspondence with C code.
* Implicit variables: variables in the untyped byte-level stack,
packing of separate logical variables inside large-enough
registers;
* Implicit loop counters/index: structures indexed by loop
counters at high-level are split into multiple low-level
computations where the link between the different logical
elements is lost.



Comments:
* This paper uses the term verification a lot, but it is not in the Hoare logic sense. It is more about formal analysis, like symbolic execution and abstract interpretation. 
* The validation process in this paper (Figure 4) is a bit circular. 