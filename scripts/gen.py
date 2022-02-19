import jinja2
import sys

templateLoader = jinja2.FileSystemLoader(searchpath="./")
templateEnv = jinja2.Environment(loader=templateLoader)


BASE_WIDTH = 32

class WordSize():
    def __init__(self, num_bits):
        # how many bits in this word size
        assert(num_bits % 8 == 0)
        self.num_bits = num_bits
        # how many bytes in this word size
        self.num_bytes = num_bits // 8

        self.align = self.num_bytes
        # how many base words to represent this word size
        assert(self.num_bits % BASE_WIDTH == 0)
        self.num_words = self.num_bits // BASE_WIDTH

sizes = [WordSize(32), WordSize(256)]

# small, big = 32, 256
# print(t.render(small=small, big=big, num_words=big//small))

# convert = templateEnv.get_template("uint_convert.jinja2")

memory = templateEnv.get_template('memory.jinja2')

print(memory.render(base_size=sizes[0], sizes=sizes))