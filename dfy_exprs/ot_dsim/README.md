# Bignum ISA Simulator

This is a simulator for a bignum accelerator.

## Usage

```bash
# Install dependencies
pip3 install --user -U -r requirements.txt

# Run the simulator
python3 sim.py

# Run the RSA tests
python3 sim_rsa_tests.py

# Run the P256 tests
python3 sim_ecc_tests.py

# Run assembler
python3 asm.py

# Run disassembler
python3 dasm.py
```

## Status

RSA encode and decode up to 2048 bit and P256 encode and decode can be
executed fully. The calculation results are cross-checked to ensure
correctness.

## Author and License

Primary author: Felix Miller

Apache2-licensed, see `LICENSE` for details.

Portions of the code in the `hex` directory are BSD-licensed, see the file
`hex/LICENSE` for details.
