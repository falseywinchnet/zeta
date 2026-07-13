# Six obligations: analytical results

## 1. Exact density forms

`density_algebra.py` reconstructs both sufficient densities from their
primitive endpoint quotients and verifies the cleared forms exactly.

For the edge density,

\[
 S_r=\frac{N_S}{A^2q(r)^2Q^2},\qquad \#N_S=24.
\]

SymPy prints the denominator as
`(-A^2 v0+A v1+u0 v0-v0^2)^2`; its base is `-A q(r) Q`, so this is the same
strictly positive denominator.  Common-subexpression elimination uses 15
temporaries.

For the full reopening density,

\[
 J_b=\frac{N_J}{B^2Cq(x)^2},\qquad \#N_J=74,
\]

and common-subexpression elimination uses 52 temporaries.  The compact source
form is preferable to committing either expanded polynomial: every temporary
is reconstructed and the result is checked against the rational density.

## 2. Exponential part and error normalization

For `t>=1`, set `X=pi exp(2t)`.  The P31 boxes are

\[
q^{(j)}(t)=2^{j+2}X(1+\eta_j e_j),\quad |e_j|\le1,
\]

with `eta_j=E_(j+2)/(2^(j+2) 128^2)` after restricting the least endpoint
scale to `X>=128`.  A primitive is written

\[
A=2(Y-X)(1+\eta_A e_A),\qquad
\eta_A=4.95/128^2.
\]

This deliberately discards the additional factors `1/U`, `1/V` in the true
primitive and endpoint errors.  At zero error the exact identities are

\[
S_r=2q(r),\qquad J_b=q(x)(B+C)(3B+C).
\]

Thus the constant coefficient in every error polynomial is the exact
exponential margin.

## 3. Proved resolved-gap tail boxes

`prove_resolved_tail.py` expands the exactly cleared numerators after
`U=2+a`, `V=2+c`, where `a,c>=0`.  For each gap monomial it subtracts the
absolute coefficient sum of every nonconstant error monomial from the exact
exponential coefficient.  Every residual coefficient is a positive rational.
This proves, without a parameter scan:

\[
\boxed{S_r(m,r)>0}
\]

when `X_m>=128` and `X_r/X_m>=2`, and

\[
\boxed{J_b(x,m,r)>0}
\]

when `X_x>=128`, `X_m/X_x>=2`, and `X_r/X_m>=2` on the positive tail.

Under reflection, odd jets change sign.  Repeating the same coefficient box
with these forced signs proves the negative-tail counterparts:

- `S_r>0` when `X_r>=128` and `X_m/X_r>=2`;
- `J_b>0` when `X_r>=128`, `X_x/X_m>=2`, and `X_m/X_r>=2`.

The direct signed calculation matters: reflection reverses the three points
and swaps the direction in which a gap is reopened, so invariance of `J_b`
itself should not be asserted.

## 4. Collision coefficients

The generic collision is `x=m-beta eps`, `r=m+alpha eps`.  P31 proved

\[
[\varepsilon^3]J=
\frac{\beta(\alpha+\beta)^2}{12q^3}C_4.
\]

`reduce_collision_eps4.py` now proves the exact reduction

\[
\boxed{
[\varepsilon^4]J=
\frac{\beta(\alpha+\beta)^2}{48q^4}
\left[
\alpha(qC_4'-2q'C_4)
+\beta(-2qC_4'+6q'C_4)
\right].}
\]

The anticipated fifth-order closure is false.  `derive_collision_eps5.py`
derives the 99-term, degree-two geometry polynomial exactly and proves it is
not in the span

\[
\{q^2C_4'',\;qq'C_4',\;qq''C_4,\;(q')^2C_4\}
\otimes\{\alpha^2,\alpha\beta,\beta^2\}.
\]

Therefore a uniform fifth-order remainder needs one additional sixth-jet
invariant.  An order-eight theta jet can bound it, but `C4,C4',C4''` alone
cannot.  This is an obstruction to the proposed proof package, not evidence
against PF4.

## 5. Escaping endpoint dominance

`derive_escape_asymptotics.py` performs exact degree extraction.  If `x,m`
are fixed and `r` tends to the positive tail (`X_r -> infinity`), then

\[
J=4D\,X_r^2+O(X_r),\qquad
J_b=4D_b\,X_r^2+O(X_r),
\]

where

\[
D=B+f(x)-M_L>0,
\]

\[
D_b=q(x)-f'(x)-\frac{q'(x)}B+\frac{M_Lq(x)}B.
\]

Thus the original PF4 numerator has proved positive dominance in this escape.
The stronger `J_b` route additionally requires `D_b>=0`, which is not yet a
theorem.  Six isolated premise tests in `probe_escape_obstruction.py` are
positive; they are diagnostics only.

If `m,r` are fixed and `x` tends to the negative tail, exact extraction gives

\[
J=8X_x^3+O(X_x^2),\qquad
J_b=48X_x^3+O(X_x^2),
\]

so both signs have unconditional leading dominance in that direction.

## 6. Status of the stronger route

No negative value of `S_r`, `J_b`, or the necessary escape coefficient `D_b`
has been found.  More importantly, no broad search was performed.  The
resolved-tail signs above are proved; the core, near-gap tail region, and the
sign of `D_b` remain open.  Failure of the fifth-order `C4`-span ansatz is the
only obstruction found this round and does not imply failure of either
density or of PF4.

