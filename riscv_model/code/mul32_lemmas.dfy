include "../spec/rsa_ops.dfy"

module mul32_lemmas {
  
    import opened bv_ops
    import opened rv_ops
    import opened rsa_ops
    import opened rv_consts

    import opened Seq
    import opened BASE_32_Seq

    lemma mulhu_bound(x: uint32, y: uint32)
      ensures uint32_mulhu(x, y) + 1 < BASE_32;
    {
      var lh := uint32_mul(x, y);
      var uh := uint32_mulhu(x, y);

      calc {
        lh + uh * BASE_32 + BASE_32;
        == { lemma_uint64_half_split(x * y); }
        x * y + BASE_32;
        <= { single_digit_lemma_0(x, y, BASE_32-1); }
        (BASE_32-1) * (BASE_32-1) + BASE_32;
        BASE_64 - 2 * BASE_32 + 1 + BASE_32;
        BASE_64 - BASE_32 + 1;
        < BASE_64;
      }
      
      if uh + 1 >= BASE_32 {
        assert false;
      }
    }

    lemma mulaa32_bound(x: uint32, y: uint32, c: uint32, d: uint32)
      ensures uint32_mulhu(x, y) * BASE_32 + uint32_mul(x, y) + c + d < BASE_64;
    {
      var lh := uint32_mul(x, y);
      var uh := uint32_mulhu(x, y);

      assert lh <= BASE_32 - 1;
      assert uh <= BASE_32 - 1;

      calc {
        lh + uh * BASE_32 + (c + d);
        == { lemma_uint64_half_split(x * y); }
        x * y + (c + d);
        <= { assert c + d <= (BASE_32-1) + (BASE_32-1); }
        x * y + (BASE_32-1) + (BASE_32-1);
        <= { single_digit_lemma_0(x, y, BASE_32-1); }
        (BASE_32-1) * (BASE_32-1) + (BASE_32-1) + (BASE_32-1);
        < { single_digit_lemma_2(BASE_32-1, BASE_32-1, BASE_32-1, BASE_32-1, BASE_32-1); }
        BASE_32 * BASE_32;
        == BASE_64;
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
            ToNatRight([x10, x11]) == a * b + c;
    {
      var lh := uint32_mul(a, b);
      var uh := uint32_mulhu(a, b);
      var carry := uint32_lt(x10, lh);

      assert x10 + BASE_32 * carry == lh + c by {
        if lh + c < BASE_32 {
          assert x10 == lh + c;
          assert carry == 0;
        } else {
          assert x10 + BASE_32 == lh + c;
          assert carry == 1;
        }
      }

      calc {
        ToNatRight([x10, x11]);
        {
          LemmaSeqLen2([x10, x11]);
        }
        x10 + x11 * BASE_32;
        x10 + uint32_add(uh, carry) * BASE_32;
        {
          mulhu_bound(a, b);
        }
        x10 + uh * BASE_32 + carry * BASE_32;
        lh + c + uh * BASE_32;
        {
          lemma_uint64_half_split(a * b);
        }
        a * b + c;
      }

    }

    lemma mulaa32_correct_lemma(
        a: uint32, // x10
        b: uint32, // x11
        c: uint32, // x12
        d: uint32, // x13
        x10: uint32,
        x11: uint32,
        x15: uint32
        )
        requires
        && x15 == uint32_add(uint32_mulhu(a, b), uint32_lt(uint32_add(c, d), c)) // uh + carry 1
        && x10 == uint32_add(uint32_mul(a, b), uint32_add(c, d))
        && x11 == uint32_add(uint32_lt(uint32_add(uint32_mul(a, b), uint32_add(c, d)), uint32_mul(a, b)), x15)
        ensures
           ToNatRight([x10, x11]) == a * b + c + d;
    {
      var lh := uint32_mul(a, b);
      var uh := uint32_mulhu(a, b);

      var s := uint32_add(c, d);
      var carry1 := uint32_lt(s, c);
      var carry2 := uint32_lt(x10, lh);

      calc {
        ToNatRight([x10, x11]);
        {
          LemmaSeqLen2([x10, x11]);
        }
        x10 + x11 * BASE_32;
        x10 + uint32_add(uint32_lt(uint32_add(lh, s), lh), x15) * BASE_32;
        x10 + uint32_add(carry2, uint32_add(uh, carry1)) * BASE_32;
        {
          mulhu_bound(a, b);
          mulaa32_bound(a, b, c, d);
        }
        x10 + uh * BASE_32 + carry1 * BASE_32 + carry2 * BASE_32;
        lh + c + d + uh * BASE_32;
        {
          lemma_uint64_half_split(a * b);
        }
        a * b + c + d;
      }
    }
      
}
