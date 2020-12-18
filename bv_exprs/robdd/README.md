# ROBDD based optimizer

Usage: `cargo run --release` starts up a loop that takes in an expression per line and tries to eliminate any variables it can from it and print it out to stdout

## Example

```
Expr:      (^ x (^ y (^ (~ (^ (^ z (^ x carry_1)) (^ (^ y (^ (^ (~ z) carry_2) carry_3)) carry_4))) carry_5)))
Optimized: (^ (^ carry_1 (^ (^ (~ carry_2) carry_3) (~ carry_4))) carry_5)
```
