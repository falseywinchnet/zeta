# Jacobian counterexample: audit and relevance

## Verdict

The mathematical disproof is real at the finite-certificate level.

For `u = 1 + xy`, define

\[
\begin{aligned}
P&=u^3z+y^2u(4+3xy),\\
Q&=y+3xu^2z+3xy^2(4+3xy),\\
R&=2x-3x^2y-x^3z.
\end{aligned}
\]

The exact local replay `verify_counterexample.py` proves

\[
\det D(P,Q,R)=-2
\]

identically and proves that the three distinct points

\[
(0,0,-1/4),\quad (1,-3/2,13/2),\quad (-1,3/2,13/2)
\]

all map to `(-1/4,0,0)`.  This is a complete counterexample to the
Jacobian conjecture in dimension three.  Appending identity coordinates extends
it to every dimension at least three.  It does not settle the plane case.

The public announcement is attributed to Levent Alpöge, who credited Fable in
the post from the night of 2026-07-19--20.  Attribution, derivation history, and
priority remain newer and less stable than the finite algebraic certificate.

## Mechanism: loss of sheets at infinity

The exact curve

\[
(x,y,z)=(s,-1/s,5/s^2)
\]

satisfies

\[
F(s,-1/s,5/s^2)=(0,2/s,0).
\]

As `|s|` tends to infinity, the source escapes while the image tends to zero.
Thus the missing global hypothesis is properness/fiber control at infinity, not
another local derivative identity.  Constant Jacobian supplies local inverses
everywhere but cannot prevent sheets from escaping and returning globally.

## Is it useful for the theta/Gaussian boundary?

Not directly.  The theta-jet estimate uses a positive absolute majorant

\[
C n^d\rho^n,\qquad 0<\rho<1,
\]

to prevent derivative mass from escaping to high summation modes.  The Jacobian
counterexample does not challenge geometric-series convergence, Gaussian decay,
or termwise differentiation under such a majorant.

There is a terminological link to the *Gaussian Moments Conjecture* of
Derksen--van den Essen--Zhao, but it is a different statement.  Their conjecture
asserts a Mathieu--Zhao closure property: if all pure Gaussian moments of a
complex polynomial vanish, then every fixed mixed moment eventually vanishes.
Their theorem says that validity of these conjectures in all dimensions would
imply the Jacobian conjecture in all dimensions.  By contrapositive, the new
counterexample proves that the Gaussian Moments Conjecture fails in at least one
finite dimension.  The published implication does not by itself exhibit the
smallest failing dimension or an explicit pair of Gaussian-moment polynomials.

That consequence is relevant only as a warning against a *moment-vanishing
closure principle*.  Our theta proof uses inequalities and absolute summability,
not such a closure principle, so its proposed non-Gaussian geometric majorant is
unaffected.

## What is genuinely useful for this repository

1. **A named escape-at-infinity audit.**  Local identities do not globalize
   without a compactness, properness, coercivity, or summable-tail mechanism.
   For infinite series the analogous audit is exactly the locally uniform tail
   majorant now isolated in P000126.
2. **A proof-engine adversarial example.**  The map is a small exact regression
   test: any general theorem or tactic that concludes global injectivity from a
   nonzero constant Jacobian alone must fail on it.
3. **A moment-closure warning.**  Do not infer eventual mixed-moment vanishing
   from pure-moment vanishing unless the needed Mathieu--Zhao property is proved
   for the precise measure and polynomial class.
4. **A possible independent research extraction.**  Chasing the explicit Keller
   map through the known reductions may produce an explicit Gaussian Moments,
   Vanishing, Image, Poisson, or Hessian counterexample.  Existing immediate
   consequences are partly existential and do not yet give a small explicit
   Gaussian-moment witness.  This is interesting but does not advance the
   Riemann-kernel cascade by itself.

## Transcript audit

The supplied ChatGPT transcript is useful as a trail but not reliable as a
proof record.  It first invented or accepted an unsupported hypergeometric
family, then retracted it, then updated after finding the Alpöge announcement.
Its exact statements about the displayed three-variable map survive independent
verification.  The proposed infinite hypergeometric family and several claimed
downstream equivalences need their own source-and-replay audits before use.

The transcript's strongest Riemann-kernel conclusion should be narrowed:
finite-order determinant data or local nondegeneracy alone does not furnish a
general local-to-global theorem.  It does **not** show that RH is independent,
unprovable, or false, and it does not constrain the reciprocal kernel `1/Xi`
without an additional functorial construction.

## Public locators consulted

- Alpöge announcement:
  https://x.com/__alpoge__/status/2079028340955197566
- Current exact explainer and replay repository:
  https://jacobianfun.org/jacobian-explained
- Current MathWorld record:
  https://mathworld.wolfram.com/JacobianConjecture.html
- Derksen--van den Essen--Zhao:
  https://arxiv.org/abs/1506.05192

These URLs are locators.  The exact map certificate and the locally stored paper
are the evidence used in this round.
