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