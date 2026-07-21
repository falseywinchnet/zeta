# Next advancement boundary

The downstream theorem now accepts exactly the natural output of the analytic
certificate: a positive raw kernel derivative jet and three cleared polynomial
signs.  The next round should construct the literal Riemann kernel at this
interface.

## Recommended order

1. Define the positive-side theta mode

   ```text
   phiMode(n,t) =
     (4*pi^2*n^4*exp(9*t/2) - 6*pi*n^2*exp(5*t/2))
       * exp(-pi*n^2*exp(2*t)).
   ```

2. Define the positive-side sum for `t >= 0` and prove summability by a single
   polynomial-times-geometric Gaussian majorant on compact intervals.
3. Define its ordinary derivative modes through order six using the recurrence
   already used by CERT12, and prove termwise differentiation.
4. Construct the global even analytic kernel through the theta transformation,
   avoiding an absolute-value definition whose smoothness at zero would be
   circular.
5. Prove equality of the global kernel jet with the positive-side certificate
   jet on `t >= 0` and use parity for `t < 0`.
6. Represent the exact CERT12 proof of `clearedQ`, `clearedF2`, and `clearedC4`
   positivity in a form Lean can replay or verify without trusting a Boolean
   label.
7. Instantiate `terminalQuotD_pos_of_clearedJetSigns` with those concrete
   functions.

The raw-Hankel identity is now closed, so the next round should not re-expand
the cumulant determinant.  Its work belongs entirely on construction,
summability, differentiation, parity, and certified raw signs.
