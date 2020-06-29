# Proof Generation Proposal:
----

# Problem:
We are given:
* an algorithm `A`: an algorithm to be implemented
* a model `M`: some Dafny code that gives a high level model (C like) of the algorithm
* a proof `P1`: some Dafny proof around `M`, certifying its correctness
* a implementation `I`: some assembly implementation of the algorithm

We would like to generate:
* a proof `P2`: a (Vale/Dafny) proof for `I`, based on `M` and `P1`

# Assumption:
* the Dafny model is "close enough" to the assembly
    
    In `M`, the subjects in the predicates need to be close enough to the ones needed in `I`. 

