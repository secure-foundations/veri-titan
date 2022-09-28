cd falcon_verify/

# gcc -O3 -Wall -fno-inline falcon_verify_alt.c -c -o native/falcon_verify_alt.o
# gcc -O3 -Wall -fno-inline falcon_verify_alt.c -S -o native/falcon_verify_alt.s
# gcc -O3 -Wall -fno-inline main.c native/falcon_verify_alt.o -o native/falcon_verify_alt.out

riscv32-unknown-elf-gcc -O3 -Wall -fno-inline falcon_verify_alt.c -c -o riscv/falcon_verify_alt.o
# riscv32-unknown-elf-gcc -O3 -Wall -fno-inline falcon_verify_alt.c -S -o riscv/falcon_verify_alt.s
riscv32-unknown-elf-gcc -O3 -Wall -fno-inline main.c riscv/falcon_verify_alt.o -o riscv/falcon_verify_alt.out

msp430-elf-gcc -O3 -Wall -fno-inline falcon_verify_alt.c -c -o msp/falcon_verify_alt.o
# msp430-elf-gcc -O3 -Wall -fno-inline falcon_verify_alt.c -S -o msp/falcon_verify_alt.s
msp430-elf-gcc -O3 -Wall -fno-inline main.c msp/falcon_verify_alt.o -o msp/falcon_verify_alt.out

cd ../rsa_verify/

riscv32-unknown-elf-gcc -O3 -Wall -fno-inline riscv/mod_exp_32.c -c -o riscv/mod_exp_32.o
riscv32-unknown-elf-gcc -O3 -Wall -fno-inline riscv/main_32.c riscv/mod_exp_32.o -o riscv/mod_exp_32.out

msp430-elf-gcc -O3 -Wall -fno-inline msp/mod_exp_16.c -c -o msp/mod_exp_16.o
msp430-elf-gcc -O3 -Wall -fno-inline msp/main_16.c msp/mod_exp_16.o -o msp/mod_exp_16.out
