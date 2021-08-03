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
        x10: uint32,
        x11: uint32,
        x15: uint32
        )
        requires
        && x10 == uint32_add(uint32_mul(a, b), c)
        && x15 == uint32_lt(x10, uint32_mul(a, b))
        && x11 == uint32_add(uint32_mulhu(a, b), x15)
        // ensures
            // to_nat([x10, x11]) == a * b + c;
    {
      single_digit_lemma_1(a, b, c, B);
      lemma_uint64_half_split(a * b);

      calc {
        to_nat([x10, x11]);
        { to_nat_lemma_1([x10, x11]); }
        x10 + x11 * B;
        uint32_add(uint32_mul(a, b), c) + uint32_add(uint32_mulhu(a, b), x15) * B;
        
      }

    }

}
