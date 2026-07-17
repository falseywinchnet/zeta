# Results

1. The apparent determinant-size advantage was partly a normalization effect:
   finite order-five determinants differ by `2^5`, and confluent coefficients
   by `2^15`, between the two papers' conventions.
2. The full-series confluent threshold candidate is
   `u_c=0.062279526635622891487943551113976...` in the current paper's
   coordinate, or `u_c/2=0.031139763317811445743971775556988...` in
   Michałowski's coordinate.
3. A 231-monomial exact three-mode polynomial approximates that full threshold
   within `9.3e-13`; this is the low-compute analytic certificate route.
4. The negative finite-spacing component extends beyond the confluent
   threshold. Its outer tangency candidate is
   `(u,h)=(0.063843571803673829...,0.046384658947623261...)`.
5. A broad log-scaled scan found no farther negative component, but did not
   certify global outermostness.
6. The most negative equal-step determinant found is instead at the origin,
   near `h=0.10553396`, with value `-1.06797481007e-7` in the paper's
   normalization.

