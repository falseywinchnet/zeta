# Strict global PF4 transport certificate

Status: refine-round audit of P000057 and P000058.  This note certifies the
exact transport identity and its implication, together with CERT3 and CERT5,
that the Riemann kernel is strictly PF4.

## Established boundaries

CERT3 proves that the fully confluent order-four central-moment determinant
`C4(t)` is strictly positive for every real `t`.  CERT5 proves that strict
global PF4 follows from

\[
 \partial_\xi\Psi(\xi;m,r)<0\qquad(\xi<m<r).
\]

The audit below connects these two previously separate boundaries.

## Curvature coordinate and sign orientation

Put

\[
 y(t)=-s(t),\qquad Q(y(t))=q(t),\qquad
 \kappa=2-Q''.
\]

CERT2 gives `q>0`, so `y` is strictly increasing and `Q>0`.  The PF3
curvature bounds give `kappa>0`.  For `p=y(xi)<z=y(m)<w=y(r)`, define the
positive triangular quantities `delta` and `Lambda` as in P000057.

If `N` denotes the P000057 transport numerator, direct differentiation of
CERT5's `Psi=Lambda+T log Lambda` gives

\[
 \boxed{\partial_\xi\Psi=-\frac{Q(p)}{\Lambda^2}\,N.}             \tag{1}
\]

The verifier checks (1) with independent generic symbols, using only
`Lambda_xi=-Q(p)delta` and commutation of translation with `partial_xi`.
Thus the orientation needed by CERT5 is `N>0`.

## Direct C4 normalization

The audit reconstructs CERT3's `C4` directly as the `4x4` central-moment
Hankel determinant in cumulants `(log Phi)^(2)..(log Phi)^(6)`.  It does not
import the thirteen-term decomposition from the advancement script.

Because differentiation in the original variable is `Q d/dy`, exact
symbolic reduction gives

\[
 \boxed{
 C_4=Q^6\kappa^2D,
 \qquad
 D=3(\kappa-1)-\{Q(\log\kappa)'\}'.}                           \tag{2}
\]

Consequently CERT3 supplies `D>0` globally.

## Exact transport identity

Normalize the triangular weights as probability measures

\[
 d\mu(y)=\frac{(z-y)\kappa(y)}{(z-p)^2\delta}
           1_{[p,z]}(y)\,dy,
\]

\[
 d\nu(y)=\frac{(y-p)\kappa(y)}{(z-p)\Lambda}1_{[p,z]}(y)\,dy
 +\frac{(w-y)\kappa(y)}{(w-z)\Lambda}1_{[z,w]}(y)\,dy.
\]

Let

\[
 A(y)=3(y-Q'(y))-Q(y)\frac{\kappa'(y)}{\kappa(y)}.
\]

Then `A'=D`.  The complete integration by parts is carried by two elementary
primitives:

\[
 \kappa A=H',\qquad H=J',                                      \tag{3}
\]

\[
 H=3y^2-3Q-3yQ'+(Q')^2+QQ'',
 \qquad J=y^3-3yQ+QQ'.                                        \tag{4}
\]

Inserting endpoint values of `J` into the two linear triangular weights and
using the endpoint formula for the chord moment `U` gives identically

\[
 \boxed{
 \frac{N}{\delta\Lambda}
 =\mathbb E_\nu[A]-\mathbb E_\mu[A].}                          \tag{5}
\]

The verifier proves (3)--(5) for an arbitrary smooth `Q`: (3)--(4) use
generic SymPy functions, and (5) is exact endpoint algebra with arbitrary
endpoint positions, values, and first derivatives.  No polynomial test,
Taylor truncation, or numerical domain cover enters the proof.

## Positive crossing kernel

Let `F_mu,F_nu` be the CDFs and `W=F_mu-F_nu`.  On `[z,w]`, `W=1-F_nu>=0`.
On `[p,z]`, the density ratio is

\[
 \frac{d\mu/dy}{d\nu/dy}
 =\frac{\Lambda(z-y)}{(z-p)\delta(y-p)}.                        \tag{6}
\]

It decreases strictly from infinity to zero.  Hence `W'` changes sign once,
from positive to negative.  Since `W(p)=0` and
`W(z)=nu([z,w])>0`, it follows that `W>0` throughout `(p,w)` and vanishes only
at the two outer endpoints.

Integration of (5) against the CDFs yields

\[
 \boxed{
 N=\delta\Lambda\int_p^w
 W(t)\frac{C_4(t)}{Q(t)^6\kappa(t)^2}\,dt>0.}                   \tag{7}
\]

Equivalently, stochastic dominance gives a monotone quantile coupling and
turns (7) into a positive double integral.  The sign-indefinite fibers of the
independent product coupling are therefore a representation artifact, not a
remaining domain.

## Consequence

CERT3 and (7) prove `N>0` for every ordered triple.  Equation (1) proves
`partial_xi Psi<0`; CERT5 then proves every order-four translate minor is
strictly positive.  Together with the lower-order results, the Riemann kernel
is strictly PF4.  The certified negative order-five minor still proves failure
of PF5, so the exact global Polya-frequency order is four.

This classification is RH-neutral.  PF4 is not PF-infinity, and the repository
already contains an exact PF4 separator whose Fourier transform has nonreal
zeros.

## Replay boundary

`scripts/verify_pf4_transport_kernel.py` checks the generic identities,
orientation, direct central-moment normalization, crossing ratio, constant
curvature regression, and two independent 70-digit Riemann-kernel comparisons.
It depends on CERT3 and CERT5; their replays supply the global `C4>0` and PF4
equivalence premises rather than duplicating their long proofs.
