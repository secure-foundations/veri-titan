include "vt_consts.dfy"
include "bv_ops.dfy"
include "vt_ops.dfy"
include "../dafny_library/NonlinearArithmetic/Power.dfy"
include "../dafny_library/NonlinearArithmetic/DivMod.dfy"
include "../dafny_library/NonlinearArithmetic/Mul.dfy"
include "../dafny_library/Sequences/NatSeq.dfy"

module refining_NatSeq refines NatSeq {
    import NT = NativeTypes
    
    function method BASE(): nat {
		NT.BASE_256
	}
}

module rsa_ops {
    import opened vt_consts
    import opened bv_ops
    import opened vt_ops
    import opened Power
    import opened DivMod 
    import opened Mul
    import NT = NativeTypes
    import opened refining_NatSeq
    import opened Seq


/* to_nat definions & lemmas */

    function {:opaque} to_nat(xs: seq<uint>): nat
    {
        refining_NatSeq.to_nat(xs)
    }

    lemma to_nat_lemma_0(xs: seq<uint>)
        requires |xs| == 1
        ensures to_nat(xs) == first(xs);
    {
        reveal to_nat();
        reveal power();
        lemma_seq_len_1(xs);
    }

    lemma to_nat_lemma_1(xs: seq<uint>)
        requires |xs| == 2
        ensures to_nat(xs) == first(xs) + last(xs) * NT.BASE_256
    {
        reveal to_nat();
        to_nat_lemma_0(drop_first(xs));
        reveal power();
        lemma_seq_len_2(xs);
    }

    lemma lsw_cong_lemma(xs: seq<uint>)
        requires |xs| >= 1;
        ensures cong_B256(to_nat(xs), xs[0]);
    {
        if |xs| == 1 {
            to_nat_lemma_0(xs);
            reveal cong();
        } else {
            assert cong_B256(to_nat(xs), xs[0]) by {
                var len' := |xs| - 1;
                var xs' := xs[..len'];

                    reveal cong();
                    lemma_power_mod(NT.BASE_256, len');
                    calc ==> {
                        pow_B256(len') % NT.BASE_256 == 0 % NT.BASE_256;
                        { lemma_mod_equivalence(pow_B256(len'), 0, NT.BASE_256); }
                        pow_B256(len') % NT.BASE_256 == 0;
                        {lemma_mul_mod_noop_general_auto();}
                        pow_B256(len') * xs[len'] % NT.BASE_256 == 0;
                        cong_B256(xs[len'] * pow_B256(len'), 0);
                    }
                    lemma_mod_equivalence(pow_B256(len') * xs[len'], 0 * xs[len'], NT.BASE_256);

                calc ==> {
                    true;
                        { 
                            reveal to_nat(); reveal cong();
                            calc ==> {
                                xs == xs' + [xs[len']];
                                {lemma_seq_eq(xs, xs' + [xs[len']]);}
                                to_nat(xs) == to_nat(xs' + [xs[len']]);
                                {lemma_seq_prefix(xs' + [xs[len']], len');}
                                to_nat(xs) == to_nat(xs') + to_nat([xs[len']]) * pow_B256(len'); 
                                { lemma_nat_seq_nat(xs[len']); to_nat_lemma_0([xs[len']]);
                                    lemma_mod_equivalence(to_nat(xs), to_nat(xs') + xs[len'] * pow_B256(len'), NT.BASE_256);}
                                is_mod_equivalent(to_nat(xs), to_nat(xs') + xs[len'] * pow_B256(len'), NT.BASE_256);
                            }
                        }
                    cong_B256(to_nat(xs), to_nat(xs') + xs[len'] * pow_B256(len'));
                    cong_B256(to_nat(xs), to_nat(xs'));
                        {
                           lsw_cong_lemma(xs');
                           assert xs'[0] == xs[0];
                           reveal cong();
                        }
                    cong_B256(to_nat(xs), xs[0]);
                }
                assert cong_B256(to_nat(xs), xs[0]);
            }
        }

    }

    lemma uint512_view_lemma(num: uint512_view_t)
        ensures num.full
            == to_nat([num.lh, num.uh])
            == num.lh + num.uh * NT.BASE_256;
    {
        reveal uint512_lh();
        reveal uint512_uh();
        to_nat_lemma_1([num.lh, num.uh]);
    }

    function seq_zero(len: nat): (zs: seq<uint>)
        ensures |zs| == len
    {
        // if len == 0 then []
        // else seq_zero(len - 1) + [0]
        reveal refining_NatSeq.seq_zero();
        refining_NatSeq.seq_zero(len)
    }

    lemma seq_zero_to_nat_lemma(len: nat)
        ensures to_nat(seq_zero(len)) == 0
    {
        reveal to_nat();
        lemma_seq_zero_nat(len);

    }

    lemma to_nat_bound_lemma(xs: seq<uint>)
        ensures to_nat(xs) < pow_B256(|xs|)
    {
            reveal to_nat();
            lemma_seq_nat_bound(xs);
    }

    lemma to_nat_zero_prepend_lemma (xs: seq<uint>)
      ensures to_nat([0] + xs) == to_nat(xs) * NT.BASE_256
    {
        reveal to_nat();
        lemma_seq_prepend_zero(xs);
    }

    lemma to_nat_prefix_lemma(xs: seq<uint>, i: nat)
        requires 0 <= i < |xs|;
        ensures to_nat(xs[..i]) + to_nat(xs[i..]) * pow_B256(i) == to_nat(xs);
    {
        reveal to_nat();
        lemma_seq_prefix(xs, i);
    }

    lemma to_nat_zero_extend_lemma(xs': seq<uint>, xs: seq<uint>) 
        requires |xs'| < |xs|
        requires var len' := |xs'|;
            && xs[..len'] == xs'
            && xs[len'.. ] == seq(|xs| - len', i => 0)
        ensures to_nat(xs') == to_nat(xs);
    {
        var len, len' := |xs|, |xs'|;
        reveal to_nat();
        if len != len' + 1 {
            var len'' := len-1;
            calc == {
                to_nat(xs);
                { lemma_seq_prefix(xs, len''); }
                to_nat(xs[..len'']) + to_nat(xs[len''..]) * pow_B256(len'');
                { to_nat_lemma_0(xs[len''..]); }
                to_nat(xs[..len'']);
                { to_nat_zero_extend_lemma(xs', xs[..len'']); }
                to_nat(xs');
            }
            assert to_nat(xs') == to_nat(xs);
        }
        ///// come back to this!!!
        else {
            assume false;
        }
    }

    function seq_addc(xs: seq<uint>, ys: seq<uint>) : (seq<uint>, uint1)
        requires |xs| == |ys|
        ensures var (zs, cout) := seq_addc(xs, ys);
            && |zs| == |xs|
    {
        reveal seq_add();
        refining_NatSeq.seq_add(xs, ys)
    }

    lemma seq_addc_nat_lemma(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: uint1)
        requires |xs| == |ys|;
        requires seq_addc(xs, ys) == (zs, cout);
        ensures to_nat(xs) + to_nat(ys) == to_nat(zs) + cout * pow_B256(|xs|)
    {
        reveal to_nat();
        reveal seq_add();
        refining_NatSeq.lemma_seq_add(xs, ys, zs, cout);
    }

    function seq_subb(xs: seq<uint>, ys: seq<uint>) : (seq<uint>, uint1)
        requires |xs| == |ys|
        ensures var (zs, bout) := seq_subb(xs, ys);
            && |zs| == |xs|
    {
        reveal to_nat();
        reveal seq_sub();
        refining_NatSeq.seq_sub(xs, ys)
    }

    lemma seq_subb_nat_lemma(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, bout: uint1)
        requires |xs| == |ys|
        requires seq_subb(xs, ys) == (zs, bout);
        ensures to_nat(xs) - to_nat(ys) + bout * pow_B256(|xs|) == to_nat(zs)
    {
        reveal to_nat();
        reveal seq_sub();
        refining_NatSeq.lemma_seq_sub(xs, ys, zs, bout);
    }

/* rsa/mm definions & lemmas */

   datatype rsa_params = rsa_params(
        M: nat, 
        M0D: uint,
        R: nat,
        RR: nat,
        R_INV: nat,
        E: nat,
        E0: uint32,
        SIG: nat,
        B256_INV: nat)

    predicate rsa_params_inv(rsa: rsa_params)
    {
        // E0 is derived from the exponent E
        && rsa.E == power(2, rsa.E0) + 1

        // modulo is none zero
        && rsa.M != 0
        && cong_B256(rsa.M0D * rsa.M, -1)

        // signature
        && rsa.SIG < rsa.M

        && rsa.R == power(NT.BASE_256, NUM_WORDS)

        && rsa.RR < rsa.M
        && cong(rsa.RR, rsa.R * rsa.R, rsa.M)

        && rsa.R_INV == power(rsa.B256_INV, NUM_WORDS)
        && cong(rsa.R_INV * rsa.R, 1, rsa.M)

        && cong(NT.BASE_256 * rsa.B256_INV, 1, rsa.M)
    }

    datatype mvars = mvars(
        x_it: iter_t,
        y_it: iter_t,

        m_it: iter_t,
        m0d_it: iter_t,
        rr_it: iter_t,
        sig_it: iter_t,
        rsa: rsa_params)

    predicate mvars_iter_init(iter: iter_t, wmem: wmem_t, address: int, value: int)
    {
        && (address != NA ==> iter_inv(iter, wmem, address))
        && (value != NA ==> to_nat(iter.buff) == value)
            && iter.index == 0
        && |iter.buff| == NUM_WORDS
    }

    predicate m0d_it_inv(iter: iter_t, wmem: wmem_t, address: int)
    {
        && (address != NA ==> iter_inv(iter, wmem, address))
        && iter.index == 0
        && |iter.buff| == 1
    }

    predicate mvars_inv(
        vars: mvars,
        wmem: wmem_t,
        x_ptr: int,
        y_ptr: int,
        m_ptr: int,
        m0d_ptr: int,
        rr_ptr: int,
        sig_ptr: int)
    {
        && rsa_params_inv(vars.rsa)

        && mvars_iter_init(vars.x_it, wmem, x_ptr, NA)
        && mvars_iter_init(vars.y_it, wmem, y_ptr, NA)
        && mvars_iter_init(vars.sig_it, wmem, sig_ptr, vars.rsa.SIG)
        && mvars_iter_init(vars.m_it, wmem, m_ptr, vars.rsa.M)
        && mvars_iter_init(vars.rr_it, wmem, rr_ptr, vars.rsa.RR)

        && m0d_it_inv(vars.m0d_it, wmem, m0d_ptr)
        && vars.m0d_it.buff[0] == vars.rsa.M0D
    }

    predicate mvars_init(
        vars: mvars,
        xmem: xmem_t,
        wmem: wmem_t,
        m_ptr: uint32,
        m0d_ptr: uint32,
        rr_ptr: uint32,
        sig_ptr: uint32,
        out_ptr: uint32)
    {
        && rsa_params_inv(vars.rsa)

        && xmem_addr_mapped(xmem, 0, vars.rsa.E0)
        && xmem_addr_mapped(xmem, 4, NUM_WORDS)
        && xmem_addr_mapped(xmem, 16, m_ptr)
        && xmem_addr_mapped(xmem, 8, m0d_ptr)
        && xmem_addr_mapped(xmem, 12, rr_ptr)
        && xmem_addr_mapped(xmem, 20, sig_ptr)
        && xmem_addr_mapped(xmem, 28, out_ptr)

        && mvars_inv(vars, wmem, NA, NA, m_ptr, m0d_ptr, rr_ptr, sig_ptr)
        && wmem_base_addr_valid(wmem, out_ptr, NUM_WORDS)

        && out_ptr != m0d_ptr
        && out_ptr != rr_ptr
        && out_ptr != m_ptr
        && out_ptr != sig_ptr
    }
}
