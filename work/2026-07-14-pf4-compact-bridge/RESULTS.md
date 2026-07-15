# Results

- Stopped the adaptive anchor generator before it produced or promoted a
  manifest.  P000056 was not replayed.
- Introduced the global curvature coordinate `y=-s(t)` and `Q(y(t))=q(t)`.
- Identified the single positive curvature function
  `kappa=2-Q''=1+h/q`, with the established bounds `14/9<kappa<=2`.
- Proved that both `Lambda` and `H/q(x)` are triangular integrals of `kappa`.
- Integrated the simultaneous-translation derivatives exactly:
  `T Lambda=U_right-U_left` and
  `T delta=(U_left-DeltaQ delta-Q(p)kappa(p))/L`.
- Obtained the closed remaining numerator (8) in
  `CURVATURE_COORDINATE.md`.  It uses only two one-dimensional transport
  moments and endpoint data; there is no residual spatial atlas.
- Reduced the local invariants to
  `C3=Q^3 kappa` and
  `C4=Q^6 kappa^2[3(kappa-1)-(Q(log kappa)')']`.
- Proved the entire constant-`Q''` model exactly: its remaining numerator is
  `(2-c)^2(1-c)(L+R)^2/4>0` whenever the PF3 condition `c<1` holds.

These are advancement identities, not a proof of global PF4.
