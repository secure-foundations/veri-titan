from bv_exprs import *

var_count = 0
bin_count = 0

def get_fresh_var():
    global var_count
    var_count += 1
    return "t%d" % var_count

def get_fresh_bin():
    global bin_count
    bin_count += 1
    return "b%d" % bin_count

def traverse_br(q):
    assert type(q) == z3.z3.BoolRef
    assert q.decl().name() == "="
    children = q.children()
    l = traverse_bvr(children[0])
    r = traverse_bvr(children[1])
    print(l + " - " + r)

def encode_and(t, l, r):
    print(f"{t} - and({l}, {r}, n)")
    # bv_and(x', y', n) == pow2(n) * bv_and(b0, b1, 1) + bv_and(x, y, n - 1)

def traverse_bvr(e):
    if type(e) == z3.z3.BitVecRef:
        children = [traverse_bvr(child) for child in e.children()]

        num_children = len(children)

        if num_children == 0:
            v = str(e.decl())
            b = get_fresh_bin()
            print(f"{v} - pow2(n) * {b} - {v}' == 0")
            return v

        op = str(e.decl())
        var = get_fresh_var()

        if op == "&":
            encode_and(var, children[0], children[1])
            return var
        else:
            raise Exception("not handled")
    elif type(e) == z3.z3.BitVecNumRef:
        return str(e)
    else:
        raise Exception("not handled")

q = bvand()
traverse_br(q)