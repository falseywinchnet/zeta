# Zeta pathway

## Current decision

The primary target is `R101`:

\[
\mathrm{RH}
\quad\Longleftrightarrow\quad
\lim_{a\to\infty}\lambda_a\ge 0,
\]

where \(\lambda_a\) is the lowest eigenvalue of Suzuki's localized Weil
operator. The curve is unconditional, continuous, positive for sufficiently
small \(a\), and nonincreasing (`R96`, `R99`, `R100`). A negative value would
disprove RH; a uniform nonnegative lower bound would prove it.

This is the cleanest surviving formulation because it compresses Weil's
infinite test family into one spectral ground-state curve while retaining the
prime-side explicit formula.

Primary local evidence:

- `CITE14`: `papers/suzuki-weil-screw.pdf`
- `CITE12`: `papers/suzuki-weil-space.pdf`

## Proof chain

1. `R78`: RH is Weil positivity.
2. `R89`: each finite interval has an unconditional lower-bounded self-adjoint
   operator \(A_a\).
3. `R99`: \(\lambda_a\) is the infimum of the Weil Rayleigh quotient over
   \(C_c^\infty(-a,a)\).
4. `R100`: nesting of test spaces makes \(\lambda_a\) nonincreasing.
5. `R96`: it is continuous and positive at small scale; false RH forces a
   negative value at finite scale.
6. `R101`: RH is equivalent to the extended large-scale limit being
   nonnegative.

Retrieve the complete chain with:

```sh
./MIND SEARCH R101
```

## Work package A: operator normalization

Reproduce the definitions and domains in `CITE14` without replacing the Weil
form by a finite matrix prematurely.

- Implement the continuous screw function \(g(t)\) from its archimedean and
  von-Mangoldt terms.
- Reproduce the quadratic form, its closed form domain, the operator \(G_a\),
  and the Friedrichs extension \(A_a\).
- Verify the small-\(a\) ground-state asymptotic and the paper's positivity,
  simplicity, and parity statements.
- Prove the test-space nesting and monotonicity in the same domain language used
  for the closed forms.

Gate A is a checked mathematical note plus convergent numerical reproduction.
Numerics alone do not establish a lower bound for the infinite-dimensional
operator.

### Integrated status

P000009 is audited in `R103`--`R111`. The fixed-interval form normalization and
the closed-domain nesting argument survive audit. Translation invariance reduces
each Dirichlet sine-basis matrix element exactly to piecewise one-dimensional
integrals (`R104`). The adaptive implementation reproduces the small-interval
scale and the finite-zero diagnostic, but its values are observations rather than
enclosures (`R105`--`R107`). In particular, the reported `a=1` value is smaller
than its scalar quadrature-error estimate (`R106`).

P000011 closes the finite-projection portion of Gate A for `N=8` at
`a=0.3,0.5,1`: Arb-directed entry and eigenvalue enclosures have positive lower
endpoints. This certifies those displayed projected matrices only. It does not
certify the full operator or advance RH. The reusable certification path splits
at exact prime powers, removes the origin analytically, respects exact parity,
and widens midpoint eigenvalues by a rigorous interval-matrix perturbation norm.

P000015 supplies the first full-operator bracket. Suzuki's exact Fourier symbol
is split as `m_a >= 1-(1-m_a)_+`. At `a=0.3` the prime sum is empty, the negative
part has certified compact frequency support, and an eight-mode Legendre
compression plus an exact directed complement trace gives (`R137`, `R138`)

\[
0.0037028625896680721
\le \lambda_{0.3}
\le 0.0101117508912467834258.
\]

The lower endpoint controls the complete form domain, not only a Galerkin
matrix. It is one finite-scale result and has no direct RH implication.

## Work package B: certified ground-state reconnaissance

Construct conforming variational approximations on nested intervals.

- Rayleigh–Ritz values provide upper bounds for \(\lambda_a\).
- A rigorously negative trial quotient would disprove RH.
- Positivity of finite Galerkin matrices does not prove \(\lambda_a\ge0\).
- Proof-directed computation must also produce certified lower bounds, using
  complementarity estimates, coercive form comparison, or resolvent bounds.
- Track every new prime-power contribution as the support interval expands.

The output is a certified bracket

\[
L(a)\le\lambda_a\le U(a),
\]

not a plot of floating-point eigenvalues.

`R109` records the variational direction: conforming Ritz minima are upper
bounds. `R135` records the successful positive compact-operator bound. The
P000011 one-block absolute-norm scheme remains retired. `R113` now asks for the
next scales: certify the small observed compact margin at `a=0.5`, then replace
that sufficient bound at `a=1` by a relative near-one cluster certificate.

## Work package C: large-scale lower bound

Use Suzuki's continuous-kernel representation to separate the localized form
into a controlled archimedean component and the finite prime contribution visible
at scale \(a\). Seek one of:

- a scale-uniform coercive inequality;
- a comparison operator with known nonnegative spectrum;
- a monotone renormalized lower bound;
- a compact-perturbation estimate whose negative part vanishes or remains
  dominated as \(a\to\infty\).

The proof target is `R102`: a nonnegative uniform lower bound, equivalently the
nonnegative endpoint in `R101`.

## Exact backup: arithmetic causal convolution

Suzuki's older arithmetic kernel gives a second exact route (`R83`): RH is
equivalent to the \(L^2\)-convolution condition for every
\(0<\omega<1/2\).

Under the logarithmic unitary map, multiplicative convolution becomes causal
additive convolution with

\[
k_\omega(r)=e^{r/2}h_\omega(e^r),\qquad \operatorname{supp}k_\omega\subset[0,\infty).
\]

The local singularities are integrable for every \(\omega>0\); the unresolved
content is global cancellation and \(L^2\) control below \(1/2\). A productive
attack must bound truncated causal operators uniformly from the arithmetic
formula, without assuming that \(\Theta_\omega\) is inner.

Calibration `R87` extends the continuous determinant construction from
\(\omega>1\) to \(\omega>1/2\). Core target `R88` addresses the RH-sensitive
range below \(1/2\).

Primary local evidence:

- `CITE7`: `papers/suzuki-canonical-system.pdf`
- `CITE8`: `papers/suzuki-integral-operators.pdf`

## Clarification-gated route

`CITE14` also constructs finite-interval characteristic functions with only real
zeros and proposes an infinite-interval limit. `R94` records a statement-level
gap: the analytic class of the normalization and the topology for the displayed
meromorphic target require clarification. Do not use that corollary as a proof
path until `R93` is resolved.

## Secondary and closed routes

- Original-kernel PF-infinity: closed (`R16`–`R18`).
- PF3/PF4 membership: closed as a sufficient real-zero mechanism by the exact
  PF4 separator (`R52`--`R54`). The Riemann kernel itself is globally PF3
  (`R140`--`R144`), so its exact global Polya-frequency order is three or four
  and only global PF4 remains open (`R145`); by Khare's Theorem E a PF4
  verification needs only the order-four minors (`R146`). The full collision
  boundary is certified positive at order four (`R147`--`R152`): every doubly
  confluent order-four minor is strictly positive, closing the route on which
  PF5 fails. PF4 remains open on the non-confluent surface, unfalsified by
  ~10^7 scanned configurations; the named continuation is certifying the
  translate Wronskians W3, W4 > 0 (ECT route, `R153`). This classification is
  RH-neutral; kernel-specific transition invariants require their own formal
  definitions.
- Jensen and Li families: exact but unbounded coordinate tests (`R62`, `R79`,
  `R85`).
- De Bruijn–Newman: exact transition boundary, but RH is the endpoint statement
  itself (`R59`–`R61`).
- DIP phase compression: failed its stated discovery criterion and lacks local
  artifacts (`R80`).
- Lagarias–Rains threshold numerics: uncertified until code and intervals are
  recovered (`R65`, `R73`).

## Retrieval discipline

Before any new zeta round:

```sh
./MIND SEARCH "localized Weil ground state lambda"
./MIND SEARCH R101
./MIND SEARCH R111
./MIND SEARCH R112
./MIND SEARCH R113
./MIND SEARCH R83
./MIND SEARCH R94
```

New computation belongs in an advancement round under `work/`. Integration,
citation, and pathway changes belong in a later refine round.
