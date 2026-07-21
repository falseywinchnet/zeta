# Next advancement

The infinite tail itself is no longer the boundary.  Advance the finite
robust three-mode theorem exposed in `RESULTS.md`.

1. Define the three-mode-relative jet
   `b_j(x,delta_j) = mode1_j + mode2_j + mode3_j*(1+delta_j)`.
2. Prove the exact identity between this definition and the right side of
   `normalizedSeriesJet_eq_first_three_relative`.
3. Recompute the cleared `q`, `F2`, and `C4` polynomials using
   `delta_j in [0,1/1000]`.  Exploit the alternating signs and the small
   relative box before falling back to coordinatewise absolute perturbation.
4. Seek a compact one-variable/exponential domination certificate.  The
   theorem must quantify over every `x>=pi` and every admissible delta vector;
   finite samples do not count.
5. Compose the finite theorem with
   `normalizedSeriesJet_eq_first_three_relative`, then with the previous
   global kernel-jet/parity bridge.  The resulting theorem should have no
   analytic or certificate premises and quantify over every real kernel
   input.

The prior 361-coefficient two-mode tables remain superseded evidence.  Do not
reintroduce the seven old arbitrary tail constants unless the structured
three-mode box is proved worse.
