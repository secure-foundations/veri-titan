import ast, pprint
import sys

pp = pprint.PrettyPrinter(indent=2)

MAIN_NAME = "Main"

class Callable:
    def _parse_formals(self, formals):
        self.formals = []
        for formal in formals:
            assert formal['ntype'] == 'Formal'
            name = formal['name']
            self.formals.append(name)

    def __init__(self, member):
        self.raw = member
        self.name = member['name']
        self.traces = []
        # print(self.name)
        if 'ins' in member:
            formals = member['ins']
        else:
            assert 'formals' in member
            formals = member['formals']
        self._parse_formals(formals)

    def add_trace(self, call):
        values = call[2:]
        assert(len(values) ==  len(self.formals))
        self.traces.append(values)

    def get_formal_concrete_value(self, name):
        index = self.formals.index(name)
        return self.traces[0][index]

class Method(Callable): 
    def __init__(self, member):
        Callable.__init__(self, member)
        self.body = member['body']

class Lemma(Callable):
    def __init__(self, member):
        Callable.__init__(self, member)

class Function(Callable):
    def __init__(self, member):
        Callable.__init__(self, member)

class DafnyParser:
    def _parse_main(self):
        main_method = self.methods[MAIN_NAME]
        stmts = main_method.body

        # the last one should be the call
        call_site = stmts[-1]

        if call_site['ntype'] == 'VarDeclStmt':
            assert len(call_site['update']['rhss']) == 1
            rhs = call_site['update']['rhss'][0]
            assert rhs['ntype'] == 'ExprRhs'
            call = rhs['expr']
            assert call['ntype'] == 'ApplySuffix'
            assert call['lhs']['name'] == self.target_name
            self.main_cs_id = call['nid']
        else:
            # pp.pprint(call_site)
            raise Exception("unhandled Main call site")

    def __init__(self, target_name) -> None:
        dfy_ast = open("ast.json").read()
        dfy_ast = ast.literal_eval(dfy_ast)

        self.methods = dict()
        self.lemmas = dict()
        self.functions = dict()
        self.target_name = target_name
        # main_method = None

        for member in dfy_ast:
            # print(member['ntype'])
            ntype = member['ntype']
            if ntype == "method":
                method = Method(member)
                self.methods[method.name] = method
            elif ntype == "lemma":
                lemma = Lemma(member)
                self.lemmas[lemma.name] = lemma
            elif ntype == "function":
                function = Function(member)
                self.functions[function.name] = function
            else:
                raise Exception("unhanled member " + ntype)

        if MAIN_NAME not in self.methods:
            raise Exception("Main method not found")

        if target_name not in self.methods:
            raise Exception("target method not found")

        self._parse_main()

    def _lookup_callee(self, name):
        if name in self.methods:
            return self.methods[name]

        if name in self.lemmas:
            return self.lemmas[name]

        if name in self.functions:
            return self.functions[name]
        
        raise Exception("callee not found")

    def get_target_method(self):
        return self.methods[self.target_name]

    def load_call(self, call):
        callee_name = call[1]
        callee = self._lookup_callee(callee_name)
        callee.add_trace(call)


if __name__ == "__main__":
    p = DafnyParser("dw_add")
