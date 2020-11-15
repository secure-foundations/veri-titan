# Proof Connection Workflow (Proposal):
----

## Inputs
* OTBN implementation of some algorithm
* Dafny implementation of the same algorithm
* Correctness proof for Dafny version
* Correlation between the inputs of the two

## Assumptions
* The two implementations cannot diverge significantly (*further clarification needed). 
* The Dafny program is written in a restricted set of Dafny. For now we are considering "large bitvector" (LBV) model, where we operate and reason about large width bit vectors that don't typically fit in single machine register or memory cell.
* The control flow is simple. For now we start experimenting with straight-line code.

## Output 
* Correctness proof for OTBN code (presumably in Vale)
* Alternatively, an equivalence proof of OTBN and LBV

## Workflow (Proposal):

Pre-process:

1. Parse OTBN/LBV code. 
2. Convert the code into SSA form.
3. Construct a DAG of use/def dependencies. Each node is an instruction/operation, associated with its output SSA variable(s). 

Equivalence guess:

1. Generate randomized inputs. Execute the two programs, label each graph node with concrete values.
2. Identify potential equivalent nodes between two graphs, starting from the sources of the graph. In this step, one LBV node might correspond to multiple OTBN nodes. (Alternatively, if we pre-split the LBV nodes at register boundaries, we might be able to look for more direct correspondence.)


<!-- To provide high assurance, cryptographic libraries are often formally verified for correctness. In some cases the verification is done on the high level source code, then a compiler is entrusted to emit the correct assembly. Alternatively, the verification can also be performed on the assembly code directly, since hand-written assembly can often achieve more optimized performance. 

Writing proofs for assembly is far from trivial. (Insert explanations on why this is hard). Writing proofs for a high level model is easier in comparison, albeit still challenging. (Insert explanations on why this is easier). 

In this work we explore a new approach towards verifying assembly implementations. Given a high-level model that is verified and a assembly implementation that needs to be verified
, we attempt to automatically derive the proof of correctness for the latter based on the former. Of course the model and the implementation cannot be arbitrary. For our purpose, we require them to be "semantically close", which we will also explore. 

A proof is consisted of pre/post conditions, invariants and additional assertions that helps it to go through. All of these are made up of predicates, which are claims about various subjects. For our purpose, the subjects of the predicates are relatively simple, where they can be:
* fixed width integers
* array of fixed width integer representing big integer
* ghost values that don't exist in the actual program flow

We note that assembly code also operate around these subjects, except that the values and pointers are stored in registers instead of variables in the high-level model. If we are able to find the correspondence, then we should be able to substitute for the subjects in the existing model to generate a proof for the assembly.  -->
