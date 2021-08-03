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

    lemma mulhu_bound(x: uint32, y: uint32)
      ensures uint32_mulhu(x, y) + 1 < BASE_32;
    {
      var lh := uint32_mul(x, y);
      var uh := uint32_mulhu(x, y);

      calc {
        lh + uh * BASE_32 + BASE_32;
        == { lemma_uint64_half_split(x * y); }
        x * y + BASE_32;
        <= { single_digit_lemma_0(x, y, BASE_32-1);}
        (BASE_32-1) * (BASE_32-1) + BASE_32;
        BASE_64 - 2 * BASE_32 + 1 + BASE_32;
        BASE_64 - BASE_32 + 1;
        < BASE_64;
      }
      
      if uh + 1 >= BASE_32 {
        assert false;
      }
    }
  
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
        ensures
            to_nat([x10, x11]) == a * b + c;
    {
      var lh := uint32_mul(a, b);
      var uh := uint32_mulhu(a, b);
      var carry := uint32_lt(x10, lh);

      assert x10 + B * carry == lh + c by {
        if lh + c < B {
          assert x10 == lh + c;
          assert carry == 0;
        } else {
          assert x10 + B == lh + c;
          assert carry == 1;
        }
      }

      calc {
        to_nat([x10, x11]);
        {
          to_nat_lemma_1([x10, x11]);
        }
        x10 + x11 * B;
        x10 + uint32_add(uh, carry) * B;
        {
          mulhu_bound(a, b);
        }
        x10 + uh * B + carry * B;
        lh + c + uh * B;
        {
          lemma_uint64_half_split(a * b);
        }
        a * b + c;
      }

    }

}
