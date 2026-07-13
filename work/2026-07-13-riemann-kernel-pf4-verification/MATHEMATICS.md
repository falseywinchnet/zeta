# Mathematical reduction: the confluent order-four boundary

## Confluent minors as moment Hankel determinants

For the smooth even Riemann kernel `Phi`, the doubly confluent limit of the
order-`k` minor `det[Phi(x_i-y_j)]` (all `x_i -> t`, all `y_j -> 0`, divided by
the two positive Vandermonde factors) is

\[
C_k(t)=(-1)^{k(k-1)/2}\,H_k(t),\qquad
H_k=\det\big[\Phi^{(i+j-2)}(t)\big]_{i,j=1}^k ,
\]

the sign coming from the `(-1)^{j-1}` produced by each `y`-derivative. PF4
therefore forces `C_4(t)>=0` for every `t`; a certified negative value would
refute PF4 outright. `C_k` is even in `t`.

Dividing by `Phi^k` and using shift invariance of moment Hankel determinants,
`H_k/\Phi^k` is the Hankel determinant of the formal central moments generated
by the cumulants `kappa_j=\ell_j=(\log\Phi)^{(j)}`:

\[
m_2=\kappa_2,\quad m_3=\kappa_3,\quad m_4=\kappa_4+3\kappa_2^2,\quad
m_5=\kappa_5+10\kappa_3\kappa_2,\quad
m_6=\kappa_6+15\kappa_4\kappa_2+10\kappa_3^2+15\kappa_2^3 .
\]

So `C_4/\Phi^4=\det[m_{i+j-2}]_{i,j=1}^4` (with `m_0=1`, `m_1=0`) is a
polynomial in exactly `\ell_2..\ell_6` — the audited P000023 jet. Expanded in
cumulants it is weight-homogeneous of weight 12 with thirteen terms:

\[
C_4=12\kappa_2^6+24\kappa_2^4\kappa_4-24\kappa_2^3\kappa_3^2
+2\kappa_2^3\kappa_6-12\kappa_2^2\kappa_3\kappa_5+7\kappa_2^2\kappa_4^2
+12\kappa_2\kappa_3^2\kappa_4+\kappa_2\kappa_4\kappa_6-\kappa_2\kappa_5^2
-9\kappa_3^4-\kappa_3^2\kappa_6+2\kappa_3\kappa_4\kappa_5-\kappa_4^3 .
\]

## Structural decomposition in PF3 invariants

Reducing modulo the 2x2 cumulant minors identifies them with the audited PF3
quantities: `\kappa_2\kappa_4-\kappa_3^2=F_1`,
`\kappa_2\kappa_5-\kappa_3\kappa_4=F_1'`,
`\kappa_2\kappa_6-\kappa_4^2=F_1''` (the identities `F_1'=qq'''-q'q''` and
`F_1''=qq''''-(q'')^2` were audited in P000024). The exact decomposition
(sympy-verified) is

\[
C_4=3\,(2q^3-F_1)(2q^3-3F_1)
+2\,(q^2F_1''-6q\dot qF_1'+9\dot q^2F_1)
-\det\begin{pmatrix}q&\dot q&\ddot q\\\dot q&\ddot q&q^{(3)}\\
\ddot q&q^{(3)}&q^{(4)}\end{pmatrix},
\]

where `2q^3-F_1=q^3+F_2>0` is the globally certified confluent order-three
minor. The Dodgson relation
`C_4\,(m_2m_4-m_3^2)=H_3^{\,\rm top}H_3^{\,\rm bot}-B^2` (with
`m_2m_4-m_3^2=F_1-3q^3<0`) also holds exactly but involves a division, so the
certifier uses the division-free forms below.

## Certification forms and derivatives

Since `d\kappa_j/du=\kappa_{j+1}`, the total derivatives of
`P=C_4(\kappa_2..\kappa_6)` are

\[
C_4'=\sum_j\frac{\partial P}{\partial\kappa_j}\kappa_{j+1},\qquad
C_4''=v^\top(\nabla^2P)\,v+\sum_j\frac{\partial P}{\partial\kappa_j}\kappa_{j+2},
\quad v_j=\kappa_{j+1},
\]

polynomials in `\kappa_2..\kappa_8`. `generate_c4_forms.py` derives all three
symbolically, checks them against a generic-jet Taylor expansion, and emits
division-free common-subexpression code (`c4_forms.py`). The cumulants through
`\kappa_8` come from the moment-cumulant recursion
`\kappa_n=r_n-\sum_{k<n}\binom{n-1}{k-1}\kappa_kr_{n-k}` on the order-eight
theta jet; the certifier's startup self-check asserts agreement with the
audited hardcoded `\ell_2..\ell_6` and with the structural decomposition
above. LU determinant evaluation of the ball Hankel matrix is rejected:
interval pivot divisions at this conditioning inflate enclosures by orders of
magnitude (the first certifier attempt did not terminate; the division-free
second-order form certifies `[0,1]` in seconds).

## Order three ties to the certified PF3 quantities

\[
C_3/\Phi^3=-\big(2\kappa_2^3+\kappa_2\kappa_4-\kappa_3^2\big)
=2q^3-F_1=q^3+F_2 .
\]

Since `q>0` and `F_2>=0` hold on all of `R` (R142-R144), every fully confluent
order-three minor is strictly positive, globally, with no new computation.
This identity is also asserted at every scan point of
`confluent_hankel_scan.py` as a cross-check.

## Cumulant tail structure

With `x=\pi e^{2u}`, `\Phi=e^{5u/2}\,4\pi x e^{-x}(1+\rho(x))`,
`w=\log(1+\rho)`, and `D=d/du=2x\,d/dx`:

- `D\log x=2`, so `D^j\log x=0` for `j\ge2`;
- `D^j x=2^j x`;
- `D^j\psi=2^j\sum_{k=1}^{j}S(j,k)\,x^k\psi^{(k)}` with Stirling subset
  numbers `S(j,k)`, by the recurrence `S(j+1,k)=kS(j,k)+S(j,k-1)`.

Hence for `j>=2`

\[
\kappa_j=\ell_j=-2^jx+\varepsilon_j,\qquad
|\varepsilon_j|\le \frac{E_j}{x},\qquad
E_j=2^j\sum_{k=1}^{j}S(j,k)\,C_k,
\]

where `|w^{(k)}|\le C_k/x^{k+1}`. For `x\ge x_0=\pi e^2>23.14` the audited
P000024 constants give `C_1..C_4=1.61,\,3.33,\,10.4,\,42.8`; extending the same
Faa di Bruno bounds two more orders (with `\rho^{(5)}=180/x^6`,
`\rho^{(6)}=-1080/x^7`, `1/v\le1.0694`, and `\sigma`-paddings absorbed):

\[
|w^{(5)}|\le\frac{222}{x^6},\qquad |w^{(6)}|\le\frac{1376}{x^7}.
\]

Term inventory for `w^{(5)}` (partition coefficients of the logarithm,
`m` blocks carry `v^{-m}`): `1\cdot\rho^{(5)}`; `5\rho^{(4)}\rho'`,
`10\rho'''\rho''`; `20\rho'''\rho'^2`, `30\rho''^2\rho'`; `60\rho''\rho'^3`;
`24\rho'^5`. Collapsed at `x_0`: `192.6+26.8+1.9+0.1 < 222`. For `w^{(6)}`:
`1\cdot\rho^{(6)}`; `6\rho^{(5)}\rho'`, `15\rho^{(4)}\rho''`, `10\rho'''^2`;
`30\rho^{(4)}\rho'^2`, `120\rho'''\rho''\rho'`, `30\rho''^3`;
`120\rho'''\rho'^3`, `270\rho''^2\rho'^2`; `360\rho''\rho'^4`; `120\rho'^6`.
Collapsed at `x_0`: `1155.5+200.3+18.6+1.0+0.1 < 1376`.

The resulting cumulant enclosure constants:

\[
E_2=19.8,\quad E_3=176,\quad E_4=2082,\quad E_5=30770,\quad E_6=545900 .
\]

`E_2, E_3, E_4` reproduce the audited P000024 tail constants exactly, because
those were the same Stirling sums; this is a structural cross-check.

## Tail lemma for C4

Substituting `\kappa_j=-2^jx+\delta_jE_j/x`, `|\delta_j|\le1`, into the moment
Hankel determinant (`tail_polynomial.py`, sympy, exact rational arithmetic):

- at `\delta=0` the determinant collapses to `H_4=49152\,x^6` exactly — every
  lower-order term cancels identically;
- every `\delta`-carrying monomial has `x`-degree at most 4;
- bounding each coefficient by its absolute sum gives
  `H_4\ge49152x^6-\sum_{d\le4}B_dx^d` with explicit rational `B_d`.

Since each `B_dx^{d-6}` is decreasing in `x`, for all `x\ge x_0=\pi e^2`

\[
H_4/x^6\;\ge\;49152-\sum_dB_dx_0^{d-6}\;>\;44392 ,
\]

evaluated exactly at the rational lower bound `x_0=2314/100<\pi e^2`. So
`C_4(u)\ge44392\,x^6>0` for `|u|\ge1`.

## Compact core

`certify_c4.py` certifies `C_4>0` on `[0,1]` with second-order Taylor cells:
tight midpoint `C_4` and `C_4'`, with only `C_4''` ball-evaluated over the
cell (radius `h|C_4'|+\tfrac{h^2}{2}\sup|C_4''|`), base step `0.002`, adaptive
bisection to depth six, 8050 cells, in seconds. Certified lower bound:
`C_4\ge2.817\cdot10^7` on `[0,1]` (output `c4-certificate.txt`; the true
minimum `1.32\cdot10^8` sits at `u=0`). Evenness extends the range to
`[-1,1]`, and the tail lemma covers `|u|\ge1`: `C_4>0` on all of `R`.

## What this does and does not settle

Certified here: every fully doubly-confluent order-four minor of the Riemann
kernel is strictly positive. This closes, at order four, exactly the boundary
route on which PF5 fails (R14: negative order-five Toeplitz minor at
`u_0=0.01`, `h=0.05`, reproduced in `toeplitz-anchor.txt`; the order-four
determinant at the same configuration is certified positive
`1.96\cdot10^{-8}`).

Not settled: global PF4 itself. The remaining surface is the non-confluent
configuration space. Probed clean in this round: translate Wronskians
`W_3, W_4` (x-collision faces, `2^{21}` Sobol samples each, no negative),
clustered minors near the PF5 failure regime and broadly (`2\times2^{21}`, no
negative), on top of the P000023 generic Sobol scan (`2^{20}`, no negative).
The ECT route to a full proof needs `W_3>0` and `W_4>0` for all translates and
all `t` — a four-parameter certification with three escape regimes — plus the
Wronskian-positivity-to-total-positivity theorem; that is the natural next
round.
