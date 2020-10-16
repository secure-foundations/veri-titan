We need to write a bunch of proofs on multiplication with `BN.MULQACC`, which is an instruction that takes in two registers, multiply selected quarter words from each register, shift the product by some amount, add the shifted result to the wacc accumulator register. For example:
```
BN.MULQACC        w0.0, w1.3, 2
```
reads from the `0` quarter word from `w0` and `3` quarter word from `w1` multiply them, shift the result by `2` quarter words (`128` bits), then add to the accumulator `wacc`. The final addition is bit vector addition, so it cuts off after `256` bits:
```
wacc = (wacc + w0.0 * w1.3 * 2 ** 128) % 2 ** 256
```

`BN.MULQACC` are typically chained together to perform longer multiplication. Here is a toy example where we compute

```
BN.MULQACC.Z      w1.0, w0.0, 0
BN.MULQACC        w1.1, w0.0, 1
BN.MULQACC        w1.0, w0.1, 1
BN.MULQACC        w1.1, w0.1, 2
```
