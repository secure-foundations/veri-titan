# Proof Generation Proposal:
----

# Problem:
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
* pre-process`P1` alongside `M`.