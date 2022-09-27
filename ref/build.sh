cd falcon_verify/

gcc -O3 falcon_verify_alt.c -c -o native/falcon_verify_alt.o
# gcc -O3 falcon_verify_alt.c -S -o native/falcon_verify_alt.s
gcc -O3 main.c native/falcon_verify_alt.o -o native/falcon_verify_alt.out

riscv32-unknown-elf-gcc -O3 falcon_verify_alt.c -c -o riscv/falcon_verify_alt.o
# riscv32-unknown-elf-gcc -O3 falcon_verify_alt.c -S -o riscv/falcon_verify_alt.s
riscv32-unknown-elf-gcc -O3 main.c riscv/falcon_verify_alt.o -o riscv/falcon_verify_alt.out

msp430-elf-gcc -O3 falcon_verify_alt.c -c -o msp/falcon_verify_alt.o
# msp430-elf-gcc -O3 falcon_verify_alt.c -S -o msp/falcon_verify_alt.s
msp430-elf-gcc -O3 main.c msp/falcon_verify_alt.o -o msp/falcon_verify_alt.out

cd ..