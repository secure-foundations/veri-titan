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

    lemma to_nat_lemma_1(xs: seq<uint256>)
        requires |xs| == 1
        ensures to_nat(xs) == xs[0]
    {
        reveal to_nat();
        reveal power();
    }

    lemma to_nat_lemma_2(xs: seq<uint256>)
        requires |xs| == 2
        ensures to_nat(xs) == xs[0] + xs[1] * BASE_256
    {
        reveal to_nat();
        to_nat_lemma_1(xs[..1]);
        reveal power();
    }

    lemma uint512_view_lemma(num: uint512_view_t)
        ensures num.full
            == to_nat([num.lh, num.uh])
            == num.lh + num.uh * BASE_256;
    {
        reveal uint512_lh();
        reveal uint512_uh();
        to_nat_lemma_2([num.lh, num.uh]);
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

    lemma to_nat_bound_lemma(x: seq<uint256>)
        ensures to_nat(x) < pow_B256(|x|)
    {
        if |x| == 0 {
            reveal to_nat();
        } else {
            assume false;
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

    lemma seq_subb_safe_nat_lemma(xs: seq<uint256>, ys: seq<uint256>)
        requires |xs| == |ys|
        requires to_nat(xs) >= to_nat(ys)
        ensures seq_subb(xs, ys).1 == 0
    {
        var (zs, bout) := seq_subb(xs, ys);
        seq_subb_nat_lemma(xs, ys, zs, bout);

        if bout == 1 {
            assert to_nat(xs) - to_nat(ys) + pow_B256(|xs|) == to_nat(zs);
            to_nat_bound_lemma(xs);
            to_nat_bound_lemma(ys);
            to_nat_bound_lemma(zs);
            assert false;
        }
    }

/* rsa/mm definions & lemmas */

   datatype pub_key = pub_key(
        e: nat, 
        m: nat,
        m0d: uint256,
        B256_INV: nat,
        R: nat,
        RR: nat,
        R_INV: nat)

    predicate pub_key_inv(key: pub_key)
    {
        && key.m != 0
        && cong_B256(key.m0d * key.m, BASE_256-1)

        && cong(BASE_256 * key.B256_INV, 1, key.m)

        && key.R == power(BASE_256, NUM_WORDS)

        && key.RR < key.m
        && cong(key.RR, key.R * key.R, key.m)

        && key.R_INV == power(key.B256_INV, NUM_WORDS)
        && cong(key.R_INV * key.R, 1, key.m)
    }

    datatype mm_vars = mm_vars(
        x_iter: iter_t,
        y_iter: iter_t,
        m_iter: iter_t,
        rr_iter: iter_t,
        m0d_iter: iter_t,
        key: pub_key)

    predicate mm_iter_inv(iter: iter_t, wmem: wmem_t, address: int)
    {
        && iter_inv(iter, wmem, address)
        && iter.index == 0
        && |iter.buff| == NUM_WORDS
    }

    predicate m0d_iter_inv(iter: iter_t, wmem: wmem_t, address: int)
    {
        && iter_inv(iter, wmem, address)
        && iter.index == 0
        && |iter.buff| == 1
    }

    predicate mm_vars_safe(
        vars: mm_vars,
        wmem: wmem_t,
        x_addr: int,
        y_addr: int,
        m_addr: int,
        rr_addr: int,
        m0d_addr: int)
    {
        && mm_iter_inv(vars.x_iter, wmem, x_addr)
        && mm_iter_inv(vars.y_iter, wmem, y_addr)

        && mm_iter_inv(vars.m_iter, wmem, m_addr)
        && mm_iter_inv(vars.rr_iter, wmem, rr_addr)
        && m0d_iter_inv(vars.m0d_iter, wmem, m0d_addr)
    }

    predicate mm_vars_inv(
        vars: mm_vars,
        wmem: wmem_t,
        x_addr: int,
        y_addr: int,
        m_addr: int,
        rr_addr: int,
        m0d_addr: int)
    {
        && pub_key_inv(vars.key)
        && mm_vars_safe(vars, wmem, x_addr, y_addr, m_addr, rr_addr,m0d_addr)
        && to_nat(vars.m_iter.buff) == vars.key.m
        && to_nat(vars.rr_iter.buff) == vars.key.RR
        && vars.m0d_iter.buff[0] == vars.key.m0d
    }
}