# Next boundary: terminal quotient and coordinate Psi

The next advancement round should address only the terminal quotient bridge.
For ordered columns `a<c<b<d`, write

```text
p_d=t-d < p_b=t-b < p_c=t-c < p_a=t-a.
```

Required exact chain:

1. identify maintained `secondQuot` and `secondQuotD` with the paper's
   `w_j` objects using the checked first- and second-level identities;
2. prove positivity of `terminalQuot` from the two derived
   `secondQuotD>0` instances;
3. factor `terminalQuotD` as `terminalQuot` times the difference
   `Psi(p_d;p_c,p_a)-Psi(p_b;p_c,p_a)`;
4. prove that this `Psi` is the same endpoint object as
   `PF4.CoordinateSignBridge.coordinatePsi`, with all coordinate substitutions
   explicit;
5. use `p_d<p_b` and strict decrease of that same `coordinatePsi` to derive
   the terminal sign.

Do not accept a new `Psi` with only a matching name, and do not assume the
terminal derivative, an order-four Wronskian sign, or a minor sign. The
analytic coordinate-sign theorem may remain a literal premise until its
Riemann-kernel instance is formalized, but the object identity and orientation
must be checked in Lean.
