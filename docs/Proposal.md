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

## Silly Example

Here is a piece of OTBN assembly. Lets assume that:
*  `w31` is zero
* `[w18, w17]` and `[w8, w9]` are the inputs, each containing a variable that spans two registers (512 bits).
* `[w20, w19]` is the output
```
test:
    bn.rshi w20, w31, w18 >> 128 // right shift [w31, w18] into w20
    bn.rshi w19, w18, w17 >> 128 // right shift [w18, w17] into w19

    bn.add w19, w19, w8 
    bn.addc w20, w20, w9 // addition with carry from the previous step
```
If we correlate `a` with `[w18, w17]`  and `b` with `[w8, w9]`, here is a Dafny model:
```
method test(a: cbv, b: cbv)
    requires |a| == 512;
    requires |b| == 512;
{
    var t1 := cbv_lsr(a, 128);
    var t2 := cbv_add(t1, b);

    important_lemma(t2, t1, a, b);
    assert important_predicate(t2);
}
```
Given those two, here is maybe what we can generate:
```
procedure test(ghost a: cbv, ghost b: cbv)
    requires
        w31 == 0;
        conacat_two(w8, w9) == a;
        conacat_two(w17, w18) == b;
    reads
        w31; w17; w18; w8; w9;
    modifies
        w19; w20; flags;
    ensures
        important_predicate(conacat_two(w19, w20));
{
    BN_RSHI(w20, w18, w31, 128); // bn.rshi w20, w18, w31 >> 128
    BN_RSHI(w19, w17, w18, 128); // bn.rshi w19, w17, w18 >> 128

    ghost var t1 := cbv_lsr(a, 128);
    assert conacat_two(w19, w20) == t1;

    BN_ADD(w19, w19, w8, false, 0, false); // bn.add w19, w19, w8
    BN_ADDC(w20, w20, w9, false, 0, false); // bn.addc w20, w20, w9

    ghost var t2 := cbv_add(t1, b);
    assert conacat_two(w19, w20) == t2;

    important_lemma(t2, t1, a, b);
    assert important_predicate(t2);
}
```

We kind of "replay" the LBV model inside the OTBN code. `important_lemma` was written for the LBV model, which ensures some `important_predicate`.

## Workflow Sketch:

Pre-process:

1. Parse OTBN/LBV code. 
2. Convert the code into SSA form.
3. Construct a DAG of use/def dependencies. Each node is an instruction/operation, associated with its output SSA variable(s).

Equivalence Guess:

1. Generate randomized inputs. Execute the two programs, label each graph node with concrete values.
2. Identify potential equivalent nodes between two graphs, starting from the sources of the graph. In this step, one LBV node might correspond to multiple OTBN nodes. (Alternatively, if we pre-split the LBV nodes at register boundaries, we might be able to look for more direct correspondence.)

Vale Code Generation:
1. Print out a Vale version of the assembly program. For the input of the Vale procedure, we additionally pass in the inputs of the LBV model, as ghosts.
2. In the procedure we also "execute" the ghost operations of the LBV model along along the Vale instructions.
3. We include the lemmas that were written for the LBV model, calling them at appropriate locations. (I guess if we are emitting SSA version of both programs, where we put the assertions or invoke lemmas shouldn't really matter too much).
4. We create assertions of equivalence (correspondence) between the concrete registers and ghost variables, as identified from the previous stage.
5. If the equivalence assertions all magically go through (BIG IF), we can also emit assertions on the register values using the high level predicates. So we end up proving high level properties about our low level program. 

<!-- To provide high assurance, cryptographic libraries are often formally verified for correctness. In some cases the verification is done on the high level source code, then a compiler is entrusted to emit the correct assembly. Alternatively, the verification can also be performed on the assembly code directly, since hand-written assembly can often achieve more optimized performance. 

Writing proofs for assembly is far from trivial. (Insert explanations on why this is hard). Writing proofs for a high level model is easier in comparison, albeit still challenging. (Insert explanations on why this is easier). 

In this work we explore a new approach towards verifying assembly implementations. Given a high-level model that is verified and a assembly implementation that needs to be verified
, we attempt to automatically derive the proof of correctness for the latter based on the former. Of course the model and the implementation cannot be arbitrary. For our purpose, we require them to be "semantically close", which we will also explore. 

A proof is consisted of pre/post conditions, invariants and additional assertions that helps it to go through. All of these are made up of predicates, which are claims about various subjects. For our purpose, the subjects of the predicates are relatively simple, where they can be:
* fixed width integers
* array of fixed width integer representing big integer
* ghost values that don't exist in the actual program flow

We note that assembly code also operate around these subjects, except that the values and pointers are stored in registers instead of variables in the high-level model. If we are able to find the correspondence, then we should be able to substitute for the subjects in the existing model to generate a proof for the assembly.  -->
