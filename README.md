

This file mainly explains the files/directories included in the artifact. 
WARNING: the artifact setup has not been tested extensively on different machines.
  
Main files/directories:

### `ref`
Contains reference implementations in either C (then compiles to assembly) or hand written assembly.

### `spec`
Should mostly contain specifications, but other files are also grouped here for convenience. Specifically, all the `*.s.dfy` are spec files (trusted to be correct), but all the `*.i.dfy` or `*.i.vad` are non-spec (verified to be correct).

### `spec/bvop`

Contains specifications for low level bitvector operations.

### `spec/arch`

Contains specifications for machine ISA semantics. For example, `spec/arch/otbn/machine.s.dfy` is the machine semantics of `OTBN`. The high level abstractions are also included, but they are verified. For example, 
`spec/arch/otbn/decls.i.vad` is the wrapper around `OTBN` semantics. There is also (trusted) printers, which print the vale code into assembly. For example, `spec/arch/msp430/printer.s.dfy` is a printer for `MSP430`.

### `spec/crypto`

Contains specifications about `Falcon`, including definitions of rings and polynomials. For example `spec/crypto/falcon.s.dfy` is the main spec for `Falcon`. However, this directory actually contains a lot of high level proofs about the correctness of NTT and polynomial multiplications, which are verified and generic over ring elements defined by `spec/crypto/ntt_param.s.dfy`. 

### `impl`

Contains the vale embedding of the 6 concrete assembly implementations. For example `impl/riscv/falcon/rv_falcon.i.vad` is the top level file of  `RISCV Falcon`. The procedure 
`rv_falcon` promises `falcon_verify` (defined in the `spec/crypto/falcon.s.dfy`) is computed. 
```
procedure rv_falcon
...
    ensures
        (a0 == 1)
            <==>
        falcon_verify(
            as_elems(iter_c0.buff), 
            as_nelems(iter_s2.buff),
            as_elems(iter_h.buff));
```
### `glue`

Contains the cross platform abstract implementations in:
 `glue/generic_falcon_lemmas.dfy` 
 `glue/generic_mm_lemmas.dfy`
 
Other folders contains the instantiations of these two modules, maybe with additional platform specific proofs that is required. 


### `std_lib`

Contains the dafny standard library.
