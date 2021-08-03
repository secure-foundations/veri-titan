include "../spec/rsa_ops.dfy"

module mul32_lemmas {
  
    import opened bv_ops
    import opened rv_ops
    import opened rsa_ops
    import opened rv_consts
    import opened powers
    import opened congruences

    const B  : int := BASE_32;
    const B2 : int := B * B;
  
    lemma mula32_correct_lemma(
        a: uint32, // x10
        b: uint32, // x11
        c: uint32, // x12

        p0: uint32, // ab lower
        p1: uint32, // ab upper

        p2: uint32, // ab + c lower
        p3: uint32,
        p4: uint32, // ab + c upper

        r0: uint64, // ab
        r1: uint64  // ab + c
        )
        
        requires
        && p0 == uint32_mul(a, b)
        && p1 == uint32_mulhu(a, b)

        && p2 == uint32_add(p0, c)
        && p3 == uint32_lt(p2, p0)
        && p4 == uint32_add(p1, p3) 
        
        && r0 == a * b
        && r1 == r0 + c
        ensures
            to_nat([p2, p4]) == a * b + c;
    {
      assert r1 == a *  b + c;
    }

}
