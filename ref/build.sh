cd falcon_verify/

# gcc -O3 -Wall -fno-inline falcon_ref.c -c -o native/falcon_ref.o
# gcc -O3 -Wall -fno-inline falcon_ref.c -S -o native/falcon_ref.s
# gcc -O3 -Wall -fno-inline main.c native/falcon_ref.o -o native/falcon_ref.out

riscv32-unknown-elf-gcc -O3 -Wall -fno-inline falcon_verify_alt.c -c -o riscv/falcon_ref.o
riscv32-unknown-elf-gcc -O3 -Wall -fno-inline main.c riscv/falcon_ref.o -o riscv/falcon_ref.elf

msp430-elf-gcc -O3 -Wall -fno-inline falcon_verify_alt.c -c -o msp/falcon_ref.o
msp430-elf-gcc -O3 -Wall -fno-inline main.c msp/falcon_ref.o -o msp/falcon_ref.elf

cd ../rsa_verify/

riscv32-unknown-elf-gcc -O3 -Wall -fno-inline riscv/mod_exp_32.c -c -o riscv/mod_exp_32.o
riscv32-unknown-elf-gcc -O3 -Wall -fno-inline riscv/main_32.c riscv/mod_exp_32.o -o riscv/mod_exp_32.elf

msp430-elf-gcc -O3 -Wall -fno-inline msp/mod_exp_16.c -c -o msp/mod_exp_16.o
msp430-elf-gcc -O3 -Wall -fno-inline msp/main_16.c msp/mod_exp_16.o -o msp/mod_exp_16.elf
