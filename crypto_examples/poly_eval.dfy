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

//    function {:opaque} poly_eval(a: seq<elem>, x: elem): elem
//    {
//        if |a| == 0 then 0
//        else modadd(First(a), modmul(poly_eval(DropFirst(a), x), x))
//    }

    function a_i_times_x_to_the_i(a: seq<elem>, x: elem): seq<elem>
    {
        seq(|a|, i requires 0 <= i < |a| => modmul(a[i], modpow(x, i)))
        //Map(i => modmul(a[i], modpow(x, i)), a)
    }
    
    function a_i_times_x_to_the_i_plus_k(a: seq<elem>, x: elem, k: nat): seq<elem>
    {
        seq(|a|, i requires 0 <= i < |a| => modmul(a[i], modpow(x, i + k)))
        //Map(i => modmul(a[i], modpow(x, i)), a)
    }

    function mod_sum(s: seq<elem>) : elem
    {
        //FoldRight((e1, e2) => modadd(e1, e2), s, 0)
        if |s| == 0 then 0
        else modadd(s[0], mod_sum(s[1..]))
    }

    lemma mod_sum_adds(s1: seq<elem>, s2: seq<elem>) 
        ensures mod_sum(s1 + s2) == modadd(mod_sum(s1), mod_sum(s2))
    {
        assume false;
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

    lemma {:axiom} modmul_distributes(x: elem, y: elem, z: elem)
        ensures modmul(x, modadd(y, z)) == modadd(modmul(x, y), modmul(x, z))
    
    lemma {:axiom} modadd_associates(x: elem, y: elem, z: elem)
        ensures modadd(x, modadd(y, z)) == modadd(modadd(x, y), z)

    lemma modadd_reassociate(a: elem, b: elem, y: elem, z: elem)
        ensures modadd(modadd(a, b), modadd(y, z)) 
             == modadd(modadd(a, y), modadd(b, z)) 
    {
        calc {
            modadd(modadd(a, b), modadd(y, z));
                { assume false; }
            modadd(modadd(a, y), modadd(b, z));
        }
    }
    
    lemma a_i_offset(a: seq<elem>, x: elem, offset:nat)
        requires |a| >= offset
        ensures a_i_times_x_to_the_i(a, x)[offset..] == a_i_times_x_to_the_i_plus_k(a[offset..], x, offset)
    {
//        var a_orig   := a_i_times_x_to_the_i(a, x)[offset..];
//        var a_offset := a_i_times_x_to_the_i_plus_k(a[offset..], x, offset);
//        assert |a_orig| == |a_offset|;
////        forall i | 0 <= i < |a_orig|
////            ensures a_orig[i] == a_offset[i];
////        {
////            calc {
////                a_orig[i];
////                modmul(a[i], modpow(x, i));
////                modmul(a[offset..][i], modpow(x, i + offset))
////                a_offset[i];
////            }
////        }
//
//
//          
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
            assume false;
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

            assume false;

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
        pow2_basics(len);
        var sqr := modmul(x, x);
        var apowers := a_i_times_x_to_the_i(a, x);
        var epowers := a_i_times_x_to_the_i(a_e, sqr);
        var opowers := a_i_times_x_to_the_i(a_o, sqr);

        assert apowers[2..] == a_i_times_x_to_the_i_plus_k(a[2..], x, 2);
        assert epowers[1..] == a_i_times_x_to_the_i_plus_k(a_e[1..], sqr, 1);
        assert opowers[1..] == a_i_times_x_to_the_i_plus_k(a_o[1..], sqr, 1);

        //assert eval_poly(a[2..], x);
        //assert mod_sum(apowers[2..]) == modadd(mod_sum(epowers[1..]), modmul(x, mod_sum(opowers[1..])));

//        calc {
//            poly_eval(a, x);
//                { reveal poly_eval(); }
//            mod_sum(a_i_times_x_to_the_i(a, x));
//            mod_sum(apowers);
//            modadd(apowers[0], modadd(apowers[1], mod_sum(apowers[2..])));
//            modadd(modmul(a[0], modpow(x, 0)), modadd(modmul(a[1], modpow(x,1)), mod_sum(apowers[2..])));
//                { LemmaPow0(x); LemmaPow1(x); }
//            modadd(modmul(a[0], 1), modadd(modmul(a[1], x), mod_sum(apowers[2..])));
//            modadd(a[0], modadd(modmul(a[1], x), mod_sum(apowers[2..])));
//
//                { assume false; } 
//                       
//            modadd(modadd(a[0], modmul(x, a[1])), modadd(mod_sum(epowers[1..]), modmul(x, mod_sum(opowers[1..]))));
//                { modadd_reassociate(a[0], mod_sum(epowers[1..]), modmul(x, a[1]), modmul(x, mod_sum(opowers[1..]))); }
//            modadd(modadd(a[0], mod_sum(epowers[1..])), modadd(modmul(x, a[1]), modmul(x, mod_sum(opowers[1..]))));
//                { modmul_distributes(x, a[1], mod_sum(opowers[1..])); }
//            modadd(modadd(a[0], mod_sum(epowers[1..])), modmul(x, modadd(a[1], mod_sum(opowers[1..]))));
//            modadd(modadd(a_e[0], mod_sum(epowers[1..])), modmul(x, modadd(a_o[0], mod_sum(opowers[1..]))));
//            modadd(modadd(modmul(a_e[0], 1), mod_sum(epowers[1..])), modmul(x, modadd(modmul(a_o[0], 1), mod_sum(opowers[1..]))));
//                { LemmaPow0(sqr); }
//            modadd(modadd(modmul(a_e[0], modpow(sqr, 0)), mod_sum(epowers[1..])), modmul(x, modadd(modmul(a_o[0], modpow(sqr, 0)), mod_sum(opowers[1..]))));
//            modadd(modadd(epowers[0], mod_sum(epowers[1..])), modmul(x, modadd(opowers[0], mod_sum(opowers[1..]))));
//            modadd(mod_sum(epowers), modmul(x, mod_sum(opowers)));
//                { reveal poly_eval(); }
//            modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
//
//        }



//        if |a| == 2 {
//            assert a_e == [a[0]];
//            assert a_o == [a[1]];
//
//            var sqr := modmul(x, x);
//
//            calc == {
//                poly_eval(a, x);
//                {
//                    reveal poly_eval();
//                    assert DropFirst(a) == a_o;
//                }
//                modadd(a[0], modmul(poly_eval(a_o, x), x));
//                {
//                    poly_eval_base_lemma(a_o, x);
//                    assert poly_eval(a_o, x) == a[1];
//                }
//                modadd(a[0], modmul(a[1], x));
//                {
//                    poly_eval_base_lemma(a_e, sqr);
//                    assert poly_eval(a_e, sqr) == a[0];
//                }
//                modadd(poly_eval(a_e, sqr), modmul(a[1], x));
//                {
//                    poly_eval_base_lemma(a_o, sqr);
//                    assert poly_eval(a_o, sqr) == a[1];
//                }
//                modadd(poly_eval(a_e, sqr), modmul(x, poly_eval(a_o, sqr)));
//            }
//            return;
//        }

        // var len' := pow2_half(len);
        // var a_ee := even_indexed_terms(a_e, len');
        // var a_eo := odd_indexed_terms(a_e, len');
        // var a_oe := even_indexed_terms(a_o, len');
        // var a_oo := odd_indexed_terms(a_o, len');

        // calc == {
        //     poly_eval(a, x);
        //     {
        //         reveal poly_eval();
        //         assert DropFirst(a) == a_o;
        //     }
        //     modadd(a[0], modmul(poly_eval(a_o, x), x));
        // }
        assume false;
    }
}
