include "../spec/bvop/bv_op.s.dfy"
include "../spec/crypto/falcon512.i.dfy"

abstract module generic_falcon_lemmas {
    import opened Mul
    import opened Power
    import opened DivMod
    import opened integers
    import opened pow2_s

    import opened ntt_index
    import opened falcon_512_i

    import FNTT = falcon_512_i.FNTT
    import INTT = falcon_512_i.INTT
    import opened MQP = falcon_512_i.CMQP

    const Q := falcon_512_i.Q;
    const N := falcon_512_i.N; 
    const OMEGA := falcon_512_i.CMQ.OMEGA;

    const R := CMQ.R;
    const PSI := CMQ.PSI;

    type floop_view = FNTT.loop_view

    type iloop_view = INTT.loop_view

    predicate {:opaque} buff_is_n_elems(a: seq<nat>)
        ensures buff_is_n_elems(a) ==> |a| == N.full;
    {
        && (|a| == N.full)
        && (forall i | 0 <= i < N.full :: a[i] < Q)
    }

    function {:opaque} buff_as_n_elems(a: seq<nat>): (a': n_elems)
        requires buff_is_n_elems(a);
        ensures a == a';
    {
        reveal buff_is_n_elems();
        a
    }

    function block_size(d: pow2_t): pow2_t
        requires CPV.block_size.requires(d)
    {
        CPV.block_size(d)
    }

    function build_floop_view(s: n_elems, d: pow2_t): floop_view
        requires FNTT.build_loop_view.requires(s, d)
    {
        FNTT.build_loop_view(s, d)
    }

    function build_iloop_view(s: n_elems, d: pow2_t): iloop_view
        requires INTT.build_loop_view.requires(s, d)
    {
        INTT.build_loop_view(s, d)
    }

    function montmul(a: elem, b: elem): elem
    {
        MQP.montmul(a, b)
    }

    function rev_mixed_powers_mont_x_value(i: nat, d: pow2_t): (r: elem)
    {
        FNTT.rev_mixed_powers_mont_x_value(i, d)
    }

    function rev_mixed_powers_mont_table(): n_elems
    {
        FNTT.rev_mixed_powers_mont_table()
    }

    function rev_omega_inv_powers_x_value(i: nat, d: pow2_t): (r: elem)
    {
        INTT.rev_omega_inv_powers_x_value(i, d)
    }

    function rev_omega_inv_powers_mont_table(): n_elems
    {
        INTT.rev_omega_inv_powers_mont_table()
    }

    function inverse_ntt_scaling_table(): n_elems
    {
        MQP.inverse_ntt_scaling_table()
    }


}