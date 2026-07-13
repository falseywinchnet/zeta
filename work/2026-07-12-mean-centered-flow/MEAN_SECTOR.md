# Mean sector

For normalized `w`, write

`p(w)=|integral w|^2/2`, `0<=p<=1`.

The exact smooth-flow inequality is

`partial_a q_a(w)>=-a^(-1)+(7/2)p(w)-||J_a||`.          (6)

Near `a=0.3`, the explicit scalar loss `1/a` and the maximum rank-one gain
`7/2` nearly cancel. Floating Ritz reconnaissance gives `p` near `0.85` for
the computed low state, stable from 8 through 32 sine modes. This identifies a
real analytic lever: a uniform lower bound on the mean of low-energy positive
states would substantially flatten the ground-state flow.

Such a bound should come from positivity improvement plus logarithmic
anti-concentration, not from a finite eigenvector. The source-normalized tools
already available are:

- the exact Fourier identity for `L`;
- the boundary logarithmic potential;
- compact embedding of the `L` form domain;
- positivity and simplicity of the small-`a` ground state.

The needed statement has the form

`q_a(w)<=E, ||w||_2=1, w>=0  =>  p(w)>=p_*(a,E)>0`.

Inserted into (6), it becomes a state-sensitive differential barrier for
`lambda_a`.
