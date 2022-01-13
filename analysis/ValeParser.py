import ast
import pprint

pp = pprint.PrettyPrinter(indent=2)
# pp.pprint(vale_ast)

REGS = set(["w0", "w1", "w2", "w3", "w4", "w5", "w6", "w7", "w8", "w9", "w10", "w11", "w12", "w13", "w14", "w15", "w16", "w17", "w18", "w19", "w20", "w21", "w22", "w23", "w24", "w25", "w26", "w27", "w28", "w29", "w30", "w31"])

FGS = set(["fg0", "fg1"])

class GFormal:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ
        self.pyhsical = None

def get_EVar_name(evar):
    assert (evar['ntype'] == "EVar")
    return evar['name']

class ValeProc:
    def _load_formals(self, formals):
        self.formals = dict()
        for formal in formals:
            assert (formal['storage'] == 'ghost ') 
            name = formal['name']
            self.formals[name] = GFormal(name, formal['type'])

    def _load_requires(self, reqs):
        for req in reqs:
            assert (req['ntype'] == 'EOp') 
            assert (req['op'] == 'Bop (BEq BpProp)') 
            assert (len(req['es']) == 2)
            left = get_EVar_name(req['es'][0])
            right = get_EVar_name(req['es'][1])
            assert left in REGS
            assert right in self.formals
            self.formals[right].pyhsical = left

    def __init__(self, ast_file):
        proc_ast = ast.literal_eval(open(ast_file).read())
        self.name = proc_ast['name']
        self._load_formals(proc_ast['formals'])
        self._load_requires(proc_ast['requires'])
