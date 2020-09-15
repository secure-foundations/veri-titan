from bv_exprs import *

var_count = 0

def traverse_br(q):
    assert type(q) == z3.z3.BoolRef
    assert q.decl().name() == "="
    children = q.children()
    l = traverse_bvr(children[0])
    r = traverse_bvr(children[1])
    print(l + " - " + r)

def encode_and(var, left, right):
    print(var + " - (" + left + " & " + right + ")")

def traverse_bvr(e):
    global var_count

    if type(e) == z3.z3.BitVecRef:
        children = [traverse_bvr(child) for child in e.children()]

        num_children = len(children)

        if num_children == 0:
            return str(e.decl())

        op = str(e.decl())
        var_count += 1
        var = "t%d" % var_count

        if num_children == 1:
            print(var + " - (" + op + " " + children[0] + ")")
            return var
        elif num_children == 2:
            # encode_and()
            print(var + " - (" + children[0] + " " + op + " " + children[1] + ")")
            return var
        else:
            raise Exception("not handled")
    elif type(e) == z3.z3.BitVecNumRef:
        print(e)
        return "1"

q = bvand()
traverse_br(q)