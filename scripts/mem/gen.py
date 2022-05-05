import jinja2
import argparse

parser = argparse.ArgumentParser(description='templated memory abstractions')
parser.add_argument('--base-width', type=int)
parser.add_argument('--heaplet-width', type=int)
parser.add_argument('--output-dir', type=str)
args = parser.parse_args()

# args = parser.parse_args('--base-width 32 --heaplet-width 256'.split())

templateLoader = jinja2.FileSystemLoader(searchpath="./")
templateEnv = jinja2.Environment(loader=templateLoader)

base_width = args.base_width
output_dir = args.output_dir
assert(base_width % 8 == 0)

class MemEntry():
    def __init__(self, num_bits, is_buff):
        self.is_buff = is_buff
        self.uint_type = f"uint{num_bits}"

        if is_buff:
            self.cons = f"B{num_bits}"
            self.name = f"b{num_bits}"
            self.type = f"seq<{self.uint_type}>"
        else:
            self.cons = f"W{num_bits}"
            self.name = f"w{num_bits}"
            self.type = self.uint_type
        self.decl = f"{self.cons}({self.name}: {self.type})"

        # how many bits in this word size
        assert(num_bits % 8 == 0)
        self.num_bits = num_bits
        # how many bytes in this word size
        self.num_bytes = num_bits // 8

        self.align = self.num_bytes
        # how many base words to represent this word size
        assert(self.num_bits % base_width == 0)
        self.num_words = self.num_bits // base_width

single = MemEntry(base_width, False)
buffer = MemEntry(args.heaplet_width, True)

with open(output_dir + "/flat.s.dfy", "w+") as f:
    flat = templateEnv.get_template('flat.jinja2')
    sizes = [single, buffer]
    if single.num_bits == buffer.num_bits:
        sizes = [single]
    f.write(flat.render(base_size=single, sizes=sizes, limit="0x80000"))

with open(output_dir + "/stack.i.dfy", "w+") as f:
    stack = templateEnv.get_template('stack.jinja2')
    f.write(stack.render(base_size=single))

with open(output_dir + "/mem.i.dfy", "w+") as f:
    mem = templateEnv.get_template('mem.jinja2')
    f.write(mem.render(base_size=single, buff_item=buffer))
