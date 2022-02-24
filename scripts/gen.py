import jinja2
import sys

templateLoader = jinja2.FileSystemLoader(searchpath="./")
templateEnv = jinja2.Environment(loader=templateLoader)


BASE_WIDTH = 32

class WordSize():
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
        assert(self.num_bits % BASE_WIDTH == 0)
        self.num_words = self.num_bits // BASE_WIDTH

sizes = [WordSize(BASE_WIDTH, False), WordSize(256, True)]
memory = templateEnv.get_template('memory.jinja2')

print(memory.render(base_size=sizes[0], sizes=sizes))