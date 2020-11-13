# Proof Connection Workflow (Proposal):
----

## Inputs
* One OTBN implementation of some algorithm
* One Dafny implementation of the same algorithm
* Correctness proof for Dafny version

## Requirements
* The two implementations cannot diverge significantly (*further clarification needed). 
* The Dafny program is written in a restricted set of Dafny. For now we are considering "large bitvector" model, where we operate and reason about large width bit vectors that don't typically fit in single machine register or memory cell.
* The control flow is simple. 

 structured and 

## Output
* Correctness proof for OTBN code (presumably in Vale)

## Workflow (Proposal):

1. Parse OTBN code. 
2. Convert the assembly into SSA form.
3. Construct a DAG of instruction dependencies. 

<!-- To provide high assurance, cryptographic libraries are often formally verified for correctness. In some cases the verification is done on the high level source code, then a compiler is entrusted to emit the correct assembly. Alternatively, the verification can also be performed on the assembly code directly, since hand-written assembly can often achieve more optimized performance. 

Writing proofs for assembly is far from trivial. (Insert explanations on why this is hard). Writing proofs for a high level model is easier in comparison, albeit still challenging. (Insert explanations on why this is easier). 

In this work we explore a new approach towards verifying assembly implementations. Given a high-level model that is verified and a assembly implementation that needs to be verified
, we attempt to automatically derive the proof of correctness for the latter based on the former. Of course the model and the implementation cannot be arbitrary. For our purpose, we require them to be "semantically close", which we will also explore. 

A proof is consisted of pre/post conditions, invariants and additional assertions that helps it to go through. All of these are made up of predicates, which are claims about various subjects. For our purpose, the subjects of the predicates are relatively simple, where they can be:
* fixed width integers
* array of fixed width integer representing big integer
* ghost values that don't exist in the actual program flow

We note that assembly code also operate around these subjects, except that the values and pointers are stored in registers instead of variables in the high-level model. If we are able to find the correspondence, then we should be able to substitute for the subjects in the existing model to generate a proof for the assembly.  -->
