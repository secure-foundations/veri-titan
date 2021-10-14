## Common commands in otbn toolcahin

`rig` uses `123` as seed and `test.yaml` as config, to generate (roughly 1000) instructions as output in `bar.json`

`hw/ip/otbn/dv/rig/otbn-rig gen --seed 123 --config test --size 1000 > bar.json`

`rig` parses `bar.json` to generate `bar.asm` and `bar.ld`

`hw/ip/otbn/dv/rig/otbn-rig asm --output bar bar.json`

`rig` parses `bar.json` to generate `bar.dfy` (we hacked on this part)

`hw/ip/otbn/dv/rig/otbn-rig dfy bar.json`

`otbn-as` assembles `bar.s` into `bar.o`

`hw/ip/otbn/util/otbn-as -o bar.o bar.s`

`otbn-as` assembles `bar.s` and `bar.ld` into `bar.elf`

`hw/ip/otbn/util/otbn-ld -o bar.elf -T bar.ld bar.o`

the python simulator runs on `bar.elf`, dumps register values in `out.dump`

`hw/ip/otbn/dv/otbnsim/standalone.py --dump-regs out.dump bar.elf`