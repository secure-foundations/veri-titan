include "generic_bv_ops.dfy"

module mul256_nl_lemma {
    import integers

    const B  : int := integers.BASE_64;
    const B2 : int := B * B;
    const B3 : int := B * B * B;
    const B4 : int := B * B * B * B;
    const B5 : int := B * B * B * B * B;
    const B6 : int := B * B * B * B * B * B;
    const B8 : int := B4 * B4;

    lemma mul256_canonize_lemma(
        p0: nat, p1: nat, p2: nat, p3: nat,
        p4: nat, p5: nat, p6: nat, p7: nat,
        p8: nat, p9: nat, p10: nat, p11: nat,
        p12: nat, p13: nat, p14: nat, p15: nat,
        x: nat, x_0: nat, x_1: nat, x_2: nat, x_3: nat,
        y: nat, y_0: nat, y_1: nat,y_2: nat, y_3: nat)

        requires
            && p0 == x_0 * y_0
            && p1 == x_1 * y_0
            && p2 == x_0 * y_1
            && p3 == x_2 * y_0
            && p4 == x_1 * y_1
            && p5 == x_0 * y_2
            && p6 == x_3 * y_0
            && p7 == x_2 * y_1
            && p8 == x_1 * y_2
            && p9 == x_0 * y_3
            && p10 == x_3 * y_1
            && p11 == x_2 * y_2
            && p12 == x_1 * y_3
            && p13 == x_3 * y_2
            && p14 == x_2 * y_3
            && p15 == x_3 * y_3
        requires
            && x == x_0 + x_1 * B + x_2 * B2 + x_3 * B3
            && y == y_0 + y_1 * B + y_2 * B2 + y_3 * B3
        ensures
            x * y
            ==
            p0 + (p1 + p2) * B + (p3 + p4 + p5) * B2 + (p6 + p7 + p8 + p9) * B3 + (p10 + p11 + p12) * B4 + (p13 + p14) * B5 + p15 * B6;
    {
    }
}