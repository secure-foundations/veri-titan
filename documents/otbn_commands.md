## Common commands in otbn toolcahin

`rig` uses `123` as seed and `test.yaml` as config, to generate (roughly 1000) instructions as output in `foo.json`

`hw/ip/otbn/dv/rig/otbn-rig gen --seed 123 --config test --size 1000 > foo.json`

`rig` parses `foo.json` to generate `foo.asm` and `foo.ld`

`hw/ip/otbn/dv/rig/otbn-rig asm --output foo foo.json`

`rig` parses `foo.json` to generate `foo.dfy` (we hacked on this part)

`hw/ip/otbn/dv/rig/otbn-rig dfy foo.json`

`otbn-as` assembles `foo.s` into `foo.o`

`hw/ip/otbn/util/otbn-as -o foo.o foo.s`

`otbn-as` assembles `foo.s` and `foo.ld` into `foo.elf`

`hw/ip/otbn/util/otbn-ld -o foo.elf -T foo.ld foo.o`

the python simulator runs on `foo.elf`, dumps register values in `out.dump`

`hw/ip/otbn/dv/otbnsim/standalone.py --dump-regs out.dump foo.elf`