# Preserved failed comparisons

The visually natural exponential constants are slightly too large for a
coefficientwise proof at `X=23`:

- `S_r >= 2 q1(r)` produces 42 negative shifted coefficients.
- `J_b >= q1(x)(B+C)(3B+C)` produces 1,026 negative shifted coefficients.

Reducing the constants to `lambda_S` and `lambda_J` makes every shifted
coefficient nonnegative.  The limiting coefficients occur at full collision,
so the loss is structural at the chosen threshold rather than a remote-gap
artifact.
