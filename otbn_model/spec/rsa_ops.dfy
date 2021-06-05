include "vt_consts.dfy"
include "bv_ops.dfy"
include "vt_ops.dfy"
include "../lib/powers.dfy"
include "../lib/congruences.dfy"

module rsa_ops {
    import opened vt_consts
    import opened bv_ops
    import opened vt_ops
    import opened powers
    import opened congruences

/* to_nat definions & lemmas */

    function {:opaque} to_nat(xs: seq<uint256>): nat
    {
        if |xs| == 0 then 0
        else
            var len' := |xs| - 1;
            to_nat(xs[..len']) + xs[len'] * pow_B256(len')
    }

    lemma to_nat_lemma_0(xs: seq<uint256>)
        requires |xs| == 1
        ensures to_nat(xs) == xs[0]
    {
        reveal to_nat();
        reveal power();
    }

    lemma to_nat_lemma_1(xs: seq<uint256>)
        requires |xs| == 2
        ensures to_nat(xs) == xs[0] + xs[1] * BASE_256
    {
        reveal to_nat();
        to_nat_lemma_0(xs[..1]);
        reveal power();
    }

    // unstable
    lemma lsw_cong_lemma(xs: seq<uint256>)
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

                assert cong_B256(xs[len'] * pow_B256(len'), 0) by {
                    reveal cong();
                    power_mod_lemma_1(BASE_256, len');
                    cong_mul_lemma_1(pow_B256(len'), 0, xs[len'], BASE_256);
                }

                calc ==> {
                    true;
                        { reveal to_nat(); reveal cong(); }
                    cong_B256(to_nat(xs), to_nat(xs') + xs[len'] * pow_B256(len'));
                        { cong_add_compose_lemma(to_nat(xs), to_nat(xs'), xs[len'] * pow_B256(len'), 0, BASE_256); }
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
            == num.lh + num.uh * BASE_256;
    {
        reveal uint512_lh();
        reveal uint512_uh();
        to_nat_lemma_1([num.lh, num.uh]);
    }

    function seq_zero(len: nat): (zs: seq<uint256>)
        ensures |zs| == len
    {
        if len == 0 then []
        else seq_zero(len - 1) + [0]
    }

    lemma seq_zero_to_nat_lemma(len: nat)
        ensures to_nat(seq_zero(len)) == 0
    {
        reveal to_nat();
    }

    lemma to_nat_bound_lemma(xs: seq<uint256>)
        ensures to_nat(xs) < pow_B256(|xs|)
    {
        reveal to_nat();
        if |xs| != 0 {
            var len' := |xs| - 1;
            calc {
                to_nat(xs);
                to_nat(xs[..len']) + xs[len'] * pow_B256(len');
                < { to_nat_bound_lemma(xs[..len']); }
                pow_B256(len') + xs[len'] * pow_B256(len');
                <= { assert xs[len'] <= BASE_256 - 1; }
                pow_B256(len') + (BASE_256 - 1) * pow_B256(len');
                BASE_256 * pow_B256(len');
                == { power_add_one_lemma(BASE_256, len'); }
                pow_B256(len' + 1);
            }
        }
    }

    lemma to_nat_zero_prepend_lemma(xs: seq<uint256>)
        ensures to_nat([0] + xs) == to_nat(xs) * BASE_256

    lemma to_nat_prefix_lemma(xs: seq<uint256>, i: nat)
        requires 1 <= i < |xs|;
        ensures to_nat(xs[..i]) == to_nat(xs[..i-1]) + xs[i-1] * pow_B256(i-1);
    {
        assert xs[..i][..i-1] == xs[..i-1];
        reveal to_nat();
    }

    lemma to_nat_zero_extend_lemma(xs': seq<uint256>, xs: seq<uint256>) 
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
                to_nat(xs[..len'']) + xs[len''] * pow_B256(len'');
                to_nat(xs[..len'']);
                { to_nat_zero_extend_lemma(xs', xs[..len'']); }
                to_nat(xs');
            }
        }
    }

    function seq_addc(xs: seq<uint256>, ys: seq<uint256>) : (seq<uint256>, uint1)
        requires |xs| == |ys|
        ensures var (zs, cout) := seq_addc(xs, ys);
            && |zs| == |xs|
    {
        if |xs| == 0 then ([], 0)
        else 
            var len' := |xs| - 1;
            var (zs', cin) := seq_addc(xs[..len'], ys[..len']);
            var (z, cout) := uint256_addc(xs[len'], ys[len'], cin);
            (zs' + [z], cout)
    }

    lemma seq_addc_nat_lemma(xs: seq<uint256>, ys: seq<uint256>, zs: seq<uint256>, cout: uint1)
        requires |xs| == |ys|;
        requires seq_addc(xs, ys) == (zs, cout);
        ensures to_nat(xs) + to_nat(ys) == to_nat(zs) + cout * pow_B256(|xs|)
    {
        reveal to_nat();
        if |xs| == 0 {
            reveal power();
        } else {
            var len' := |xs| - 1;
            var (zs', cin) := seq_addc(xs[..len'], ys[..len']);
            var (z, _) := uint256_addc(xs[len'], ys[len'], cin);
            assert xs[len'] + ys[len'] + cin == z + cout * BASE_256;

            calc {
                to_nat(zs);
                to_nat(zs') + z * pow_B256(len');
                    { seq_addc_nat_lemma(xs[..len'], ys[..len'], zs', cin); }
                to_nat(xs[..len']) + to_nat(ys[..len']) - cin * pow_B256(len') + z * pow_B256(len');
                to_nat(xs[..len']) + to_nat(ys[..len']) + xs[len'] * pow_B256(len') 
                    + ys[len'] * pow_B256(len') - cout * BASE_256 * pow_B256(len');
                    { reveal to_nat(); }
                to_nat(xs) + to_nat(ys) - cout * BASE_256 * pow_B256(len');
                    { reveal power(); }
                to_nat(xs) + to_nat(ys) - cout * pow_B256(|xs|);
            }
            assert to_nat(zs) + cout * pow_B256(|xs|) == to_nat(xs) + to_nat(ys);
        }
    }

    function seq_subb(xs: seq<uint256>, ys: seq<uint256>) : (seq<uint256>, uint1)
        requires |xs| == |ys|
        ensures var (zs, bout) := seq_subb(xs, ys);
            && |zs| == |xs|
    {
        if |xs| == 0 then ([], 0)
        else 
            var len' := |xs| - 1;
            var (zs, bin) := seq_subb(xs[..len'], ys[..len']);
            var (z, bout) := uint256_subb(xs[len'], ys[len'], bin);
            (zs + [z], bout)
    }

    lemma seq_subb_nat_lemma(xs: seq<uint256>, ys: seq<uint256>, zs: seq<uint256>, bout: uint1)
        requires |xs| == |ys|
        requires seq_subb(xs, ys) == (zs, bout);
        ensures to_nat(xs) - to_nat(ys) + bout * pow_B256(|xs|) == to_nat(zs)
    {
        reveal to_nat();
        if |xs| == 0 {
            reveal power();
        } else {
            var len' := |xs| - 1;
            var (zs', bin) := seq_subb(xs[..len'], ys[..len']);
            var (z, _) := uint256_subb(xs[len'], ys[len'], bin);
            assert bout * BASE_256 + xs[len'] - bin - ys[len'] == z;
            
            calc {
                to_nat(zs);
                to_nat(zs') + z * pow_B256(len');
                    { seq_subb_nat_lemma(xs[..len'], ys[..len'], zs', bin); }
                to_nat(xs[..len']) - to_nat(ys[..len']) + bin * pow_B256(len') + z * pow_B256(len');
                to_nat(xs[..len']) - to_nat(ys[..len']) + xs[len'] * pow_B256(len')
                    - ys[len'] * pow_B256(len') + bout * BASE_256 * pow_B256(len');
                    { reveal to_nat(); }
                to_nat(xs) - to_nat(ys) + bout * BASE_256 * pow_B256(len');
                    { reveal power(); }
                to_nat(xs) - to_nat(ys) + bout * pow_B256(|xs|);
            }
        }
    }

/* rsa/mm definions & lemmas */

   datatype rsa_params = rsa_params(
        M: nat,
        M0D: uint256,

        R: nat,
        RR: nat,

        E: nat,
        E0: uint32,

        SIG: nat,

        B256_INV: nat,

        R_INV: nat)

    predicate rsa_params_inv(rsa: rsa_params)
    {
        && rsa.E == power(2, rsa.E0) + 1

        && rsa.M != 0
        && cong_B256(rsa.M0D * rsa.M, -1)

        && cong(BASE_256 * rsa.B256_INV, 1, rsa.M)

        && rsa.SIG < rsa.M

        && rsa.R == power(BASE_256, NUM_WORDS)

        && rsa.RR < rsa.M
        && cong(rsa.RR, rsa.R * rsa.R, rsa.M)

        && rsa.R_INV == power(rsa.B256_INV, NUM_WORDS)
        && cong(rsa.R_INV * rsa.R, 1, rsa.M)
    }

    datatype mm_vars = mm_vars(
        x_it: iter_t,
        y_it: iter_t,

        m_it: iter_t,
        m0d_it: iter_t,
        rr_it: iter_t,
        sig_it: iter_t,
        rsa: rsa_params)


    predicate mm_iter_init(iter: iter_t, wmem: wmem_t, address: int, value: int)
    {
        && (address != NA ==> iter_inv(iter, wmem, address))
        && (value != NA ==> to_nat(iter.buff) == value)
        && iter.index == 0
        && |iter.buff| == NUM_WORDS
    }

    predicate m0d_it_inv(iter: iter_t, wmem: wmem_t, address: int)
    {
        && iter_inv(iter, wmem, address)
        && iter.index == 0
        && |iter.buff| == 1
    }

    predicate mm_vars_inv(
        vars: mm_vars,
        wmem: wmem_t,

        x_ptr: int,
        y_ptr: int,

        m_ptr: int,
        m0d_ptr: int,
        rr_ptr: int,
        sig_ptr: int)
    {
        && rsa_params_inv(vars.rsa)

        && mm_iter_init(vars.x_it, wmem, x_ptr, NA)
        && mm_iter_init(vars.y_it, wmem, y_ptr, NA)
        && mm_iter_init(vars.sig_it, wmem, sig_ptr, vars.rsa.SIG)
        && mm_iter_init(vars.m_it, wmem, m_ptr, vars.rsa.M)
        && mm_iter_init(vars.rr_it, wmem, rr_ptr, vars.rsa.RR)

        && m0d_it_inv(vars.m0d_it, wmem, m0d_ptr)
        && vars.m0d_it.buff[0] == vars.rsa.M0D
    }

    predicate mm_vars_init(
        vars: mm_vars,
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

        && mm_vars_inv(vars, wmem, NA, NA, m_ptr, m0d_ptr, rr_ptr, sig_ptr)
        && wmem_base_addr_valid(wmem, out_ptr, NUM_WORDS)

        && out_ptr != m0d_ptr
        && out_ptr != rr_ptr
        && out_ptr != m_ptr
        && out_ptr != sig_ptr
    }
}