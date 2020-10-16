We need to write a bunch of proofs on multiplication with `BN.MULQACC`, which is an instruction that takes in two registers, multiply selected quarter words from each register, shift the product by some amount, add the shifted result to the wacc accumulator register. For example:
```
BN.MULQACC        w0.0, w1.3, 2
```
reads from the `0` quarter word from `w0` and `3` quarter word from `w1` multiply them, shift the result by `2` quarter words (`128` bits), then add to the accumulator `wacc`. The final addition is bit vector addition, so it cuts off after `256` bits:
```
wacc = (wacc + w0.0 * w1.3 * 2 ** 128) % 2 ** 256
```

`BN.MULQACC` can be chained together to perform longer multiplication. Here is a toy example where we compute the `256` bit product of the lower `128` bits of  `w28` and `w29`.

```
BN.MULQACC.Z      w28.0, w29.0, 0
BN.MULQACC        w28.1, w29.0, 1
BN.MULQACC        w28.0, w29.1, 1
BN.MULQACC        w28.1, w29.1, 2
```

What makes it tricky to use algebraic solver on that directly is the bit vector addition, which might or might not overflow. We can introduce some unconstrained boolean variables, which indicates the overflow bit. 

```
ring r=integer,(w28, w28_h0, w28_h1, w28_q0, w28_q1, w28_q2, w28_q3,
    w29, w29_h0, w29_h1, w29_q0, w29_q1, w29_q2, w29_q3,
    wacc_g1, wacc_g2, wacc_g3, wacc_g4, B, k_0, k_1, k_2),lp;

ideal I =
    w28 - w28_h0 - w28_h1 * B^2, // w28 is made of two half words
    w28_h0 - w28_q0 - w28_q1 * B, // lower half word is made of two quarter words
    w28_h1 - w28_q2 - w28_q3 * B,  // higher half word is made of two quarter words

    w29 - w29_h0 - w29_h1 * B^2, // same deal in w29
    w29_h0 - w29_q0 - w29_q1 * B,
    w29_h1 - w29_q2 - w29_q3 * B,

    wacc_g1 - w28_q0 * w29_q0, // MULQACC.Z, which clears the initial wacc
    wacc_g2 - wacc_g1 - w28_q1 * w29_q0 * B - k_0 * B^4, // since we don't know if overflow happened or not, we put k_0 here
    wacc_g3 - wacc_g2 - w28_q0 * w29_q1 * B - k_1 * B^4,
    wacc_g4 - wacc_g3 - w28_q1 * w29_q1 * B^2 - k_2 * B^4,

    k_0 * (k_0 - 1), // the overflow bits
    k_1 * (k_1 - 1),
    k_2 * (k_2 - 1);

ideal G = groebner(I);
reduce(wacc_g4 - w28_h0 * w29_h0, G);
```

Not very surprisingly, `Singular` cannot reduce `wacc_g4 - w28_h0 * w29_h0` to `0`, instead it gives:

```
B^4*k_0+B^4*k_1+B^4*k_2
```
We note that
* `B` is not `0`. So if `k_i` are all `0`, the reduction would be be `0`. 
* For some small `B`, for example `B = 1`, we can confirm the term is `0` by exhaustively checking, which means `k_i` are all `0`. Sadly the implication does not work the other way around, we can't tell if `k_i` are all `0` when `B!=1`.
* However this does put the focus on the `k_i`. 