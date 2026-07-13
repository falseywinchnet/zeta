# The Wronskian route: PF4 as a three-point monotonicity criterion

All identities below were validated numerically to ~50 digits
(`validate_reduction.py`) before being recorded.

## Quotient reduction and the iterated-integral criterion

For `y_1 < y_2 < y_3 < y_4` put `u_j(t) = Phi(t-y_j)`,
`v_j = (u_j/u_1)'` for `j>=2`, and `w_j = (v_j/v_2)'` for `j>=3`. The
classical quotient identities give

\[
W(u_1,u_2)=u_1^2(u_2/u_1)',\quad
W(u_1,u_2,u_3)=u_1^3W(v_2,v_3),\quad
W(u_1,\dots,u_4)=u_1^4W(v_2,v_3,v_4),
\]
\[
W(v_2,v_3,v_4)=v_2^3W(w_3,w_4),\qquad
W(w_3,w_4)=w_3^2\,(w_4/w_3)' .
\]

Row-differencing collocation determinants yields the iterated-integral
expansion: with `U_j=u_j/u_1`,

\[
\det[u_j(t_i)]_{k}=\prod_i u_1(t_i)\cdot
\int_{t_1}^{t_2}\!\!\cdots\int_{t_{k-1}}^{t_k}
\det[v_j(\tau_i)]_{k-1}\,d\tau,
\]

and again one level down. Consequently, entirely self-contained:

**Criterion.** If `q>0` on `R` (so `v_j>0`), if `(v_3/v_2)'>0` for every
translate pair (so all `w_j>0` and every order-3 minor is positive), and if
`(w_4/w_3)'>0` for every translate triple, then every order-`<=4` collocation
minor of `Phi` is strictly positive: strict global TP4. No external
Chebyshev-system theorem is needed.

## Mean objects

For `a<b` define `A(a,b)=s(a)-s(b)=\int_a^b q>0`,
`M(a,b)=(q(b)-q(a))/A(a,b)` (the `q`-weighted mean of `f=q'/q`), and
`N(a,b)=(q'(b)-q'(a))/A(a,b)`. Under the translation generator `T=d/dt`
(all points moving together):

\[
T\log A=M,\qquad TM=N-M^2 .
\]

Points are written `p_j=t-y_j`, so `p_4<p_3<p_2<p_1`.

## Order three: W3 > 0 is already certified

`L_3:=T\log(v_3/v_2)=A(p_3,p_2)+M(p_3,p_1)-M(p_2,p_1)`. Splitting the mean
over `[p_3,p_1]` at `p_2` gives the exact factorization

\[
L_3=\frac{A(p_3,p_2)}{A(p_3,p_1)}\;\Lambda(p_3;p_2,p_1),\qquad
\Lambda(\xi;m,r):=A(\xi,r)+M(\xi,m)-M(m,r),
\]

and `\Lambda` is exactly the audited R141 slope functional, bounded below by
`\int_\xi^r\min(q^3,F_2)/q^2>0` under the certified `q>0`, `F_2>0`
(R141-R143). Hence `W_3(t;y)>0` for every translate triple and every `t`:
all order-three minors of the Riemann kernel, including every x-confluent
one, are strictly positive. This is a theorem given P000023/P000024; no new
computation is involved.

## Order four: the collapse to a single monotonicity

`L_4:=T\log(w_4/w_3)`. Writing `g_j=T\log(v_j/v_2)` (so `g_j=L_3` with
`p_3\mapsto p_j`) and using the mean-splitting identities

\[
M(p_j,p_2)-M(p_j,p_1)=\frac{A(p_2,p_1)\,\Lambda_j}{A(p_j,p_1)}-A(p_2,p_1),
\qquad g_j=\frac{A(p_j,p_2)\,\Lambda_j}{A(p_j,p_1)},
\]

every intermediate term cancels and (validated exactly)

\[
L_4=\big[\Lambda_4+T\log\Lambda_4\big]-\big[\Lambda_3+T\log\Lambda_3\big]
=\Psi(p_4;p_2,p_1)-\Psi(p_3;p_2,p_1),
\]

where `\Psi(\xi;m,r):=\Lambda(\xi;m,r)+T\log\Lambda(\xi;m,r)`. Since `p_4<p_3`
range freely below `p_2`:

**Reduction theorem.** Global PF4 of the Riemann kernel is equivalent to

\[
\partial_\xi\Psi(\xi;m,r)\le0
\qquad\text{for all }\xi<m<r,
\]

a smooth pointwise criterion in three real parameters (strict inequality
gives strict TP4). The same self-similar shape governs order three:
`L_3=\Delta[A+T\log A]` with the order-two object `A`; order four is
`L_4=\Delta[\Lambda+T\log\Lambda]` with the order-three object `\Lambda`. The
known failure of PF5 (R14) means the analogous order-five statement must
fail; the ladder breaks exactly one level up.

## Closed forms

Everything is rational in the jet `(s,q,q',q'')` at the three points:

\[
\Lambda=A(\xi,r)+M(\xi,m)-M(m,r),\qquad
T\Lambda=(q(r)-q(\xi))+\big(N(\xi,m)-M(\xi,m)^2\big)-\big(N(m,r)-M(m,r)^2\big),
\]
\[
\Lambda_\xi=-q(\xi)+\frac{q(\xi)M(\xi,m)-q'(\xi)}{A(\xi,m)},\qquad
\partial_\xi T\Lambda=-q'(\xi)+\frac{N(\xi,m)q(\xi)-q''(\xi)}{A(\xi,m)}
-\frac{2M(\xi,m)\big(q(\xi)M(\xi,m)-q'(\xi)\big)}{A(\xi,m)},
\]
\[
\partial_\xi\Psi=\Lambda_\xi+\frac{(\partial_\xi T\Lambda)\Lambda-(T\Lambda)\Lambda_\xi}{\Lambda^2}.
\]

`\Lambda` is invariant under the reflection `(\xi,m,r)\mapsto(-r,-m,-\xi)`
(`A` invariant, `M` anti-invariant), which pairs the `\xi`- and `r`-escape
regimes.

## Numerical stability and the scan

Evaluating the jet from theta-series ratios loses `\sim\log_{10}(2x)^4`
digits to cancellation in `\ell_4`; beyond `|u|\approx2.5` float64 output is
garbage (an early scan produced spurious positives at `|u|\sim18`, refuted at
140 digits — the true values there are `\approx-q(\xi)<0`). The scanner
therefore switches at `|u|=1` to the exact x-frame identities
`\ell_j=-2^jx+2^j\sum_kS(j,k)x^kw^{(k)}` (audited Stirling structure, no
cancellation), with branch agreement at the switch to 11 digits.

Scan results (`psi_scan.py`, `psi-scan.json`): four regimes (core, wide,
collision-targeted, extreme; `2^{21}` Sobol samples each, 8.4 million total),
zero values of `\partial_\xi\Psi` above `-4.8`, `\Lambda>0` everywhere. The
observed global maximum `\approx-4.80` sits at the full-collision boundary
near `t=0`; escapes behave as `\partial_\xi\Psi\approx-q(\xi)\to-\infty`.

## Status toward certification

The criterion has a uniform observed margin (`\le-4.8`) and closed forms in
an already-certified jet. The certification plan is: (i) the confluent limit
of `\partial_\xi\Psi` (all three points colliding) is a one-dimensional
function of the jet at `t` — certify it like q, F1, F2, C4; (ii) compact
three-dimensional core by directed interval cells in
`(m,\log g_L,\log g_R)`; (iii) three escape lemmas from the x-frame
enclosures (E_2..E_4 constants suffice; the criterion needs nothing beyond
`q''`). Not executed this round.
