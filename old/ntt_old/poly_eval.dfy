include "pow2.dfy"
include "omega.dfy"

module poly_eval {
    import opened Seq
    import opened Power
    import opened Power2
    import opened DivMod
    import opened Mul
    import opened pows_of_2
    import opened omegas

    function a_i_times_x_to_the_i(a: seq<elem>, x: elem): seq<elem>
    {
        seq(|a|, i requires 0 <= i < |a| => modmul(a[i], modpow(x, i)))
        //Map(i => modmul(a[i], modpow(x, i)), a)
    }
    
    function a_i_times_x_to_the_i_plus_k(a: seq<elem>, x: elem, k: nat): seq<elem>
    {
        seq(|a|, i requires 0 <= i < |a| => modmul(a[i], modpow(x, i + k)))
    }

    function mod_sum(s: seq<elem>) : elem
    {
        //FoldRight((e1, e2) => modadd(e1, e2), s, 0)
        if |s| == 0 then 0
        else modadd(s[0], mod_sum(s[1..]))
    }

    lemma mod_sum2(s: seq<elem>)
      requires |s| == 2;
      ensures mod_sum(s) == modadd(s[0], s[1])
    {
      assert mod_sum(s) == modadd(s[0], mod_sum(s[1..]));
    }

    lemma mod_sum_adds(s1: seq<elem>, s2: seq<elem>) 
        ensures mod_sum(s1 + s2) == modadd(mod_sum(s1), mod_sum(s2))
    {
      if |s1| == 0 {
        assert mod_sum(s1) == 0;
        assert s1 + s2 == s2;
      } else {
        calc {
          mod_sum(s1 + s2);
            { assert (s1 + s2)[1..] == s1[1..] + s2; }
          modadd(s1[0], mod_sum(s1[1..] + s2));
            { mod_sum_adds(s1[1..], s2); }
          modadd(s1[0], modadd(mod_sum(s1[1..]), mod_sum(s2)));
            { modadd_associates(s1[0], mod_sum(s1[1..]), mod_sum(s2)); }
          modadd(modadd(s1[0], mod_sum(s1[1..])), mod_sum(s2));
          modadd(mod_sum(s1), mod_sum(s2));
        }
      }
    }
    
    function {:opaque} poly_eval(a: seq<elem>, x: elem): elem
    {
        mod_sum(a_i_times_x_to_the_i(a, x))
    }

    function {:opaque} poly_eval_offset(a: seq<elem>, x: elem, offset: nat): elem
    {
        mod_sum(a_i_times_x_to_the_i_plus_k(a, x, offset))
    }

    function method odd_indexed_terms(a: seq<elem>, len: pow2_t): seq<elem>
        requires |a| == len.full * 2;
    {
        seq(len.full, n requires 0 <= n < len.full => a[n * 2 + 1])
    }

    function method even_indexed_terms(a: seq<elem>, len: pow2_t): seq<elem>
        requires |a| == len.full * 2;
    {
        seq(len.full, n requires 0 <= n < len.full => a[n * 2])
    }

    lemma poly_eval_base_lemma(a: seq<elem>, x: elem)
        requires |a| == 1;
        ensures poly_eval(a, x) == a[0];
    {
        calc {
            poly_eval(a, x);
                { reveal poly_eval(); }
            mod_sum(a_i_times_x_to_the_i(a, x));
                calc {
                    a_i_times_x_to_the_i(a, x);
                    [modmul(a[0], modpow(x, 0))];
                    calc {
                        modmul(a[0], modpow(x, 0));
                            { LemmaPow0(x); }
                        modmul(a[0], 1 % Q);
                        a[0];
                    }
                    [a[0]];
                }
            mod_sum([a[0]]);
            a[0];
        }
        
    }

    lemma modmul_distributes(x: elem, y: elem, z: elem)
        ensures modmul(x, modadd(y, z)) == modadd(modmul(x, y), modmul(x, z))
    {
      calc {
        modmul(x, modadd(y, z));
        (x * ((y + z) % Q)) % Q;
          { LemmaMulModNoopGeneral(x, y+z, Q); }
        (x * (y + z)) % Q;
          { LemmaMulIsDistributiveAdd(x, y, z); }
        (x * y + x * z) % Q;
          { LemmaAddModNoop(x*y, x*z, Q); }
        (((x * y) % Q) + ((x * z) % Q)) % Q;
        (modmul(x, y) + modmul(x, z)) % Q;
        modadd(modmul(x, y), modmul(x, z));
      }
    }
    
    lemma modmul_associates(x: elem, y: elem, z: elem)
        ensures modmul(x, modmul(y, z)) == modmul(modmul(x, y), z)
    {
      calc {
        modmul(x, modmul(y, z));
        (x * ((y * z) % Q)) % Q;
          { LemmaMulModNoopGeneral(x, y*z, Q); }
        (x * (y * z)) % Q;
          { LemmaMulIsAssociative(x, y, z); }
        ((x * y) * z) % Q;
          { LemmaMulModNoopGeneral(x*y, z, Q); }
        (((x * y) % Q) * z) % Q;
        modmul(modmul(x, y), z);
      }
    }

    lemma modadd_associates(x: elem, y: elem, z: elem)
        ensures modadd(x, modadd(y, z)) == modadd(modadd(x, y), z)
    {
      calc {
        modadd(x, modadd(y, z));
        (x + ((y + z) % Q)) % Q;
          { LemmaAddModNoop(x, y+z, Q); }
        (x + (y + z)) % Q;
          { assert x + (y + z) == (x + y) + z; }
        ((x + y) + z) % Q;
          { LemmaAddModNoop(x+y, z, Q); }
        (((x + y) % Q) + z) % Q;
        modadd(modadd(x, y), z);
      }
    }

    lemma modadd_reassociate(a: elem, b: elem, y: elem, z: elem)
        ensures modadd(modadd(a, b), modadd(y, z)) 
             == modadd(modadd(a, y), modadd(b, z)) 
    {
        calc {
            modadd(modadd(a, b), modadd(y, z));
              { modadd_associates(a, b, modadd(y, z)); }
            modadd(a, modadd(b, modadd(y, z)));
              { modadd_associates(b, y, z); }
            modadd(a, modadd(modadd(b, y), z));
              { assert modadd(b, y) == modadd(y, b); }
            modadd(a, modadd(modadd(y, b), z));
              { modadd_associates(y, b, z); }
            modadd(a, modadd(y, modadd(b, z)));
              { modadd_associates(a, y, modadd(b, z)); }
            modadd(modadd(a, y), modadd(b, z));
        }
    }
    
    lemma modpow_group(x:elem, offset:nat)
      ensures modpow(modmul(x, x), offset) == modpow(x, 2*offset)
      ensures modmul(x, modpow(x, 2*offset)) == modpow(x, 1+2*offset)
    {
      calc {
        modpow(modmul(x, x), offset);
        Pow((x * x) % Q, offset) % Q;
          { LemmaPowModNoop(x*x, offset, Q); }
        Pow(x * x, offset) % Q;
          { reveal Pow(); assert Pow(x, 2) == x * x; }
        Pow(Pow(x, 2), offset) % Q;
          { LemmaPowMultiplies(x, 2, offset); }
        Pow(x, 2*offset) % Q;
        modpow(x, 2*offset);
      }
      
      calc {
        modmul(x, modpow(x, 2*offset));
        modmul(x, Pow(x, 2*offset) % Q);
        (x * (Pow(x, 2*offset) % Q)) % Q;
          { LemmaMulModNoopGeneral(x, Pow(x, 2*offset), Q); }
        (x * Pow(x, 2*offset)) % Q;
          { reveal Pow(); }
        Pow(x, 1+2*offset) % Q;
        modpow(x, 1+2*offset);
      }
    }


    lemma poly_eval_split_lemma_helper(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>, len: pow2_t, x: elem, offset:nat)
        requires |a| == len.full * 2;
        requires a_e == even_indexed_terms(a, len)
        requires a_o == odd_indexed_terms(a, len)
        ensures var sqr := modmul(x, x);
            poly_eval_offset(a, x, 2*offset)
                == 
            modadd(poly_eval_offset(a_e, sqr, offset), modmul(x, poly_eval_offset(a_o, sqr, offset)));
        decreases |a|;
    {
        if |a| == 2 {
            assert a_e == [a[0]];
            assert a_o == [a[1]];

            var sqr := modmul(x, x);

            calc == {
                poly_eval_offset(a, x, 2*offset);
                  { reveal poly_eval_offset(); }
                mod_sum(a_i_times_x_to_the_i_plus_k(a, x, 2*offset));
                  {
                    assert a_i_times_x_to_the_i_plus_k(a, x, 2*offset) ==
                          [modmul(a[0], modpow(x, 2*offset)), 
                           modmul(a[1], modpow(x, 1 + 2*offset))];
                  }
                mod_sum([modmul(a[0], modpow(x, 2*offset)), 
                         modmul(a[1], modpow(x, 1 + 2*offset))]);
                  { mod_sum2([modmul(a[0], modpow(x, 2*offset)), modmul(a[1], modpow(x, 1 + 2*offset))]); }
                modadd(modmul(a[0], modpow(x, 2*offset)), 
                       modadd(modmul(a[1], modpow(x, 1 + 2*offset)), 0));
                modadd(modmul(a[0], modpow(x, 2*offset)), 
                       modmul(a[1], modpow(x, 1 + 2*offset)));
                  { modpow_group(x, offset); }
                modadd(modmul(a[0], modpow(sqr, offset)), 
                      modmul(a[1], modmul(x, modpow(sqr, offset)))); 
                  { modmul_associates(a[1], x, modpow(sqr, offset)); }
                modadd(modmul(a[0], modpow(sqr, offset)), 
                      modmul(modmul(a[1], x), modpow(sqr, offset))); 
                modadd(modmul(a[0], modpow(sqr, offset)), 
                      modmul(modmul(x, a[1]), modpow(sqr, offset))); 
                  { modmul_associates(x, a[1], modpow(sqr, offset)); }
                modadd(modmul(a[0], modpow(sqr, offset)), 
                      modmul(x, modmul(a[1], modpow(sqr, offset)))); 
//                  { 
//                    mod_sum2([modmul(a[0], modpow(sqr, offset))]); 
//                    mod_sum2([modmul(a[1], modpow(sqr, offset))]);
//                  }
                modadd(mod_sum([modmul(a[0], modpow(sqr, offset))]), 
                      modmul(x, mod_sum([modmul(a[1], modpow(sqr, offset))]))); 
                modadd(mod_sum([modmul(a_e[0], modpow(sqr, offset))]), 
                      modmul(x, mod_sum([modmul(a_o[0], modpow(sqr, offset))]))); 
                  { 
                    reveal poly_eval_offset(); 
                    assert a_i_times_x_to_the_i_plus_k(a_e, sqr, offset) ==
                           [modmul(a_e[0], modpow(sqr, offset))];
                    assert a_i_times_x_to_the_i_plus_k(a_o, sqr, offset) ==
                           [modmul(a_o[0], modpow(sqr, offset))];
                  }
                modadd(poly_eval_offset(a_e, sqr, offset), modmul(x, poly_eval_offset(a_o, sqr, offset)));
            }
        } else {
            var sqr := modmul(x, x);
            var apowers := a_i_times_x_to_the_i_plus_k(a, x, 2*offset);
            var epowers := a_i_times_x_to_the_i_plus_k(a_e, sqr, offset);
            var opowers := a_i_times_x_to_the_i_plus_k(a_o, sqr, offset);

            //assert eval_poly(a[2..], x);
            calc {
                Pow2(0);
                    { LemmaPow2(0); }
                Pow(2, 0);
                    { LemmaPow0(2); }
                1;
            }
            assert len.exp > 0;
            var new_len := pow2_t_cons(len.full / 2, len.exp-1);
            // Prove new_len is well_formed
            calc {
                new_len.full;
                len.full / 2;
                Pow2(len.exp) / 2;
                    { reveal Pow2(); reveal Pow(); }
                Pow2(len.exp - 1);
                Pow2(new_len.exp);
            }
            calc {
                new_len.full * 2;
                (len.full / 2) * 2;
                (Pow2(len.exp) / 2) * 2;
                    { reveal Pow2(); LemmaPowAdds(2, 1, len.exp - 1); }
                ((Pow2(1) * Pow2(len.exp - 1)) / 2) * 2;
                    { reveal Pow2(); LemmaPow1(2); }
                ((2 * Pow2(len.exp - 1)) / 2) * 2;
                    { LemmaDivMultiplesVanish(Pow2(len.exp - 1), 2); }
                Pow2(len.exp - 1) * 2;
                    { reveal Pow2(); reveal Pow(); }
                Pow2(len.exp); 
                len.full;
            }


            assert apowers[len.full..]   == a_i_times_x_to_the_i_plus_k(a[len.full..], x, len.full + 2*offset);
            assert epowers[len.full/2..] == a_i_times_x_to_the_i_plus_k(a_e[len.full/2..], sqr, len.full/2 + offset);
            assert opowers[len.full/2..] == a_i_times_x_to_the_i_plus_k(a_o[len.full/2..], sqr, len.full/2 + offset);
            
            assert apowers[..len.full]   == a_i_times_x_to_the_i_plus_k(a[..len.full], x, 2*offset);
            assert epowers[..len.full/2] == a_i_times_x_to_the_i_plus_k(a_e[..len.full/2], sqr, offset);
            assert opowers[..len.full/2] == a_i_times_x_to_the_i_plus_k(a_o[..len.full/2], sqr, offset);

            assert (len.full/2 + offset) * 2 == len.full + 2*offset;

            calc {
                poly_eval_offset(a, x, 2*offset);
                    { reveal poly_eval_offset(); }
                mod_sum(apowers);
                    { 
                        mod_sum_adds(apowers[..len.full], apowers[len.full..]);  
                        assert apowers == apowers[..len.full] + apowers[len.full..]; 
                    }
                modadd(mod_sum(apowers[..len.full]), mod_sum(apowers[len.full..]));
                    { reveal poly_eval_offset(); }
                modadd(poly_eval_offset(a[..len.full], x, 2*offset), poly_eval_offset(a[len.full..], x, len.full + 2*offset));
                    { 
                        poly_eval_split_lemma_helper(a[..len.full], a_e[..len.full/2], a_o[..len.full/2], new_len, x, offset); 
                        assert even_indexed_terms(a[..len.full], new_len) == a_e[..len.full/2];
                        assert  odd_indexed_terms(a[..len.full], new_len) == a_o[..len.full/2];
                    }
                modadd(modadd(poly_eval_offset(a_e[..len.full/2], sqr, offset), modmul(x, poly_eval_offset(a_o[..len.full/2], sqr, offset))), poly_eval_offset(a[len.full..], x, len.full + 2*offset));
                    { 
                        poly_eval_split_lemma_helper(a[len.full..], a_e[len.full/2..], a_o[len.full/2..], new_len, x, len.full/2 + offset); 
                        assert even_indexed_terms(a[len.full..], new_len) == a_e[len.full/2..];
                        assert  odd_indexed_terms(a[len.full..], new_len) == a_o[len.full/2..];
                    }
                modadd(modadd(poly_eval_offset(a_e[..len.full/2], sqr, offset), modmul(x, poly_eval_offset(a_o[..len.full/2], sqr, offset))),
                       modadd(poly_eval_offset(a_e[len.full/2..], sqr, len.full/2 + offset), modmul(x, poly_eval_offset(a_o[len.full/2..], sqr, len.full/2 + offset))));
                    { modadd_reassociate(poly_eval_offset(a_e[..len.full/2], sqr, offset), modmul(x, poly_eval_offset(a_o[..len.full/2], sqr, offset)),
                                         poly_eval_offset(a_e[len.full/2..], sqr, len.full/2 + offset), modmul(x, poly_eval_offset(a_o[len.full/2..], sqr, len.full/2 + offset))); }
                modadd(modadd(poly_eval_offset(a_e[..len.full/2], sqr, offset), poly_eval_offset(a_e[len.full/2..], sqr, len.full/2 + offset)),
                       modadd(modmul(x, poly_eval_offset(a_o[..len.full/2], sqr, offset)), modmul(x, poly_eval_offset(a_o[len.full/2..], sqr, len.full/2 + offset))));
                    { modmul_distributes(x, poly_eval_offset(a_o[..len.full/2], sqr, offset), poly_eval_offset(a_o[len.full/2..], sqr, len.full/2 + offset)); }
                modadd(modadd(poly_eval_offset(a_e[..len.full/2], sqr, offset), poly_eval_offset(a_e[len.full/2..], sqr, len.full/2 + offset)), 
                       modmul(x, modadd(poly_eval_offset(a_o[..len.full/2], sqr, offset), poly_eval_offset(a_o[len.full/2..], sqr, len.full/2 + offset)))); 
                    { reveal poly_eval_offset(); }
                modadd(modadd(mod_sum(epowers[..len.full/2]), mod_sum(epowers[len.full/2..])), modmul(x, modadd(mod_sum(opowers[..len.full/2]), mod_sum(opowers[len.full/2..]))));
                    { 
                        mod_sum_adds(epowers[..len.full/2], epowers[len.full/2..]);  
                        assert epowers == epowers[..len.full/2] + epowers[len.full/2..]; 
                        mod_sum_adds(opowers[..len.full/2], opowers[len.full/2..]);  
                        assert opowers == opowers[..len.full/2] + opowers[len.full/2..]; 
                    }
                modadd(mod_sum(epowers), modmul(x, mod_sum(opowers)));
                    { reveal poly_eval_offset(); }
                modadd(poly_eval_offset(a_e, sqr, offset), modmul(x, poly_eval_offset(a_o, sqr, offset)));
            }
        }
    }

    
    lemma poly_eval_split_lemma(a: seq<elem>, 
        a_e: seq<elem>, a_o: seq<elem>, len: pow2_t, x: elem)
        requires |a| == len.full * 2;
        requires a_e == even_indexed_terms(a, len)
        requires a_o == odd_indexed_terms(a, len)
        ensures var sqr := modmul(x, x);
            poly_eval(a, x)
                == 
            modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
        decreases |a|;
    {
      poly_eval_split_lemma_helper(a, a_e, a_o, len, x, 0);
      reveal poly_eval();
      reveal poly_eval_offset();
      var sqr := modmul(x, x);
      // OBSERVE: Seq extensionality
      assert a_i_times_x_to_the_i(a, x) == a_i_times_x_to_the_i_plus_k(a, x, 0);
      assert a_i_times_x_to_the_i(a_e, sqr) == a_i_times_x_to_the_i_plus_k(a_e, sqr, 0);
      assert a_i_times_x_to_the_i(a_o, sqr) == a_i_times_x_to_the_i_plus_k(a_o, sqr, 0);
      assert poly_eval(a, x) == poly_eval_offset(a, x, 0);
    }
}
