from bv_exprs import *

tmp_count = 0
bin_count = 0
input_vars = dict()
opaque_vars = dict()

def get_fresh_tmp():
    global tmp_count
    tmp_count += 1
    return "t%d" % tmp_count

def get_fresh_bin():
    global bin_count
    bin_count += 1
    b = "b%d" % bin_count
    print(f"{b} * (1 - {b})")
    return b

def get_fresh_opaque(actual):
    global opaque_vars

    if actual in opaque_vars:
        return opaque_vars[actual]

    o = "o%d" % (len(opaque_vars) + 1) 
    opaque_vars[actual] = o
    return o

def add_input_var(v):
    global input_vars

    if v not in input_vars:
        b = get_fresh_bin()
        input_vars[v] = b
        print(f"{v}' - pow2_n * {b} - {v}")

def get_assoc_bin(v):
    global input_vars
    if v not in input_vars:
        raise Exception("not an input var")
    return input_vars[v]

def traverse_br(q, goal):
    assert type(q) == z3.z3.BoolRef
    assert q.decl().name() == "="
    children = q.children()
    l = traverse_bvr(children[0], goal)
    r = traverse_bvr(children[1], goal)
    print(l + " - " + r)

def encode_and(t, l, r, goal):
    if goal:
        o0 = get_fresh_opaque(f"bv_and({l}, {r}, n)")
        print(f"{t} - {o0}")
    else:
        o0 = get_fresh_opaque(f"bv_and({l}, {r}, n - 1)")
        print(f"{t} - {o0}")

        bl = get_assoc_bin(l)
        br = get_assoc_bin(r)

        b = get_fresh_bin()
        print(f"{b} - {bl} * {br}")

        o1 = get_fresh_opaque(f"bv_and({l}', {r}', n)")
        print(f"{o1} - pow2_n * {b} - {o0}")

def traverse_bvr(e, goal):
    if type(e) == z3.z3.BitVecRef:
        children = [traverse_bvr(child, goal) for child in e.children()]

        num_children = len(children)

        if num_children == 0:
            v = str(e.decl())
            if goal:
                return v + "'"
            else:
                add_input_var(v)
                return v

        op = str(e.decl())
        var = get_fresh_tmp()

        if op == "&":
            encode_and(var, children[0], children[1], goal)
            return var
        else:
            raise Exception("not handled")
    elif type(e) == z3.z3.BitVecNumRef:
        return str(e)
    else:
        raise Exception("not handled")

q = bvand()
traverse_br(q, False)
print("")
traverse_br(q, True)