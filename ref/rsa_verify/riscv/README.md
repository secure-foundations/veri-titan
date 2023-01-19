Simple self-contained example to demonstrate SW based RSA signature verification on RV32IMC

**Build:**

`riscv32-unknown-elf-gcc -O2 -fno-inline -march=rv32imc -Wall rsa_rv.c -o rsa_rv.elf`

`cc1: error: requested ABI requires '-march' to subsume the 'D' extension`

if it shows the error above, use: 

`riscv32-unknown-elf-gcc -O2 -fno-inline -Wall rsa_rv.c -o rsa_rv.elf`

inline version:

`riscv32-unknown-elf-gcc -O2 -Wall rsa_rv.c -o rsa_rv.elf`

with `-fno-inline` to preserve all subroutines in assemnly output, which
might be helpful to individually verify the subroutines. Remove flag if
not needed.

**Simulate:**
`spike --isa=RV32IMC <path to pk>/pk rsa_rv.elf`

**Algorithm**
The Algorithms used are standard square-and-multiply and Montgomery
multiplication for modular multiplication.
The Montgomery implementation is a variant of the FIOS method of [1]. Probably
Algorithm 2 of [2] is what comes closest to this in literature.
We omit the comparison against the key's modulus in the Montgomery loop and
only compare against the Montgomery Radix. This is fine as long as there is
a final comparison and conditional subtraction at the very end of the modular
exponentiation. A justification for this can be found in [3].

**Assembly**
Assembyl in the dump file was obtained using `objdump`. Calling conventions
are standard (see e.g. https://place-holder

**References**  
[1] https://place-holder  
[2] https://place-holder  
[3] https://place-holder  
