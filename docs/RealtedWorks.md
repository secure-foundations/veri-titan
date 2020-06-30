# Related Works:
----

## Get rid of inline assembly through verification-oriented lifting
----
Inline assembly code is often needed along side with C code. The problem is that inline assembly makes formal analysis on the code difficult. Say I have some tool that works on C, it will not be able to handle the inline assembly parts.

This paper describes an approach to "decompile" the inline assembly code into C code, in a way that is amenable towards formal analysis. 

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

Overall Work Flow:
* Compilation: the source code is compiled with debugging symbols
* IR lifting: the binary is then lifted into a simple IR.
* C lifting: the IR is translated into C code
* Validation: the decompiled C code is validated. 

The last two steps are the meat of their work.

There are several difficulties are in the IR -> C step:

* Low-level data: explicit flags, including overflows or
carry, bitwise operations (masks), low-level comparisons they don't have good correspondence with C code.

    To address this issue, they refer to an external technique that can prove equivalence of low level predicates. So instead of control flow condition depending on a bit in the flag register, it will depend on expressions from registers.

* Implicit variables: separate logical variables could be packed inside a large register. like different parts of the same register corresponds to different C variables. 

    To address this, we used something called register unpacking. They basically split up register to 8/16/32 bit sizes. Then they see if any of them is being used and assign a variable to it. Unused ones are eliminated. 

    They also talk about expression propagation. From my understanding they are propagating symbolic values, aggregating them into expressions, then a simplification pass happens over the expressions. 

* Implicit loop counters/index: structures indexed by loop
counters at high-level are split into multiple low-level
computations where the link between the different logical
elements is lost.



Comments:
* This paper uses the term verification a lot, but it is not in the Hoare logic sense. It is more about formal analysis, like symbolic execution and abstract interpretation. 
* The validation process in this paper (Figure 4) is a bit circular. 