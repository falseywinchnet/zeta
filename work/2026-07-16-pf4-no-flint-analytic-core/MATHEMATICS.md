# A sweep-free two-mode proof candidate

## 1. Normalization

For `u>=0` put

\[
x=\pi e^{2u},\qquad P_0(t)=2t-3,
\]

and define

\[
P_{j+1}(t)=\left(\frac52-2t\right)P_j(t)+2tP_j'(t).
\]

Then the `j`th derivative of the `n`th theta mode is

\[
2\pi n^2 e^{5u/2-n^2x}P_j(n^2x).
\]

Factor the positive first mode. With `y=e^{-3x}`, the normalized derivatives
of the first two modes are

\[
a_j(x,y)=\frac{P_j(x)+4yP_j(4x)}{P_0(x)}.
\tag{1}
\]

The normalized contribution of all later modes is

\[
e_j(x)=\sum_{n\ge3}
\frac{n^2e^{-(n^2-1)x}P_j(n^2x)}{P_0(x)}.
\tag{2}
\]

Machin's formula gives `pi>157/50`, hence `x>157/50` and `P0(x)>0`.

## 2. Cleared raw invariants

For a derivative vector `(a0,...,a6)`, the three sign-bearing numerators are

\[
N_q=a_1^2-a_0a_2,
\]

\[
\begin{aligned}
N_{F_2}={}&-a_0^4a_2a_4+a_0^4a_3^2+a_0^3a_1^2a_4
-2a_0^3a_1a_2a_3+2a_0^3a_2^3\\
&-3a_0^2a_1^2a_2^2+3a_0a_1^4a_2-a_1^6,
\end{aligned}
\]

and

\[
N_{C_4}=\det[a_{i+j}]_{i,j=0}^3.
\]

If `f` is the normalized kernel value, then

\[
q=\frac{N_q}{f^2},\qquad F_2=\frac{N_{F_2}}{f^6},\qquad
\mathcal C_4=\frac{N_{C_4}}{f^4}.
\tag{3}
\]

The verifier reconstructs (3) symbolically. It also reconstructs the
thirteen-term cumulant formula for `C4` from the central-moment determinant,
so the two representations are not merely assumed to agree.

## 3. Closed first-mode formulas

For the first mode alone, exact differentiation gives

\[
q_1=\frac{4x(4x^2-12x+15)}{(2x-3)^2},
\]

\[
(F_2)_1=\frac{64x^3(64x^6-576x^5+2448x^4-6432x^3
+10044x^2-8100x+2295)}{(2x-3)^6},
\]

\[
(C_4)_1=\frac{49152x^6(16x^4-96x^3+360x^2-840x+945)}{(2x-3)^4}.
\]

After `x=5+z`, every numerator coefficient is positive. The same is true for
the first two derivatives of all three expressions. Thus the dominant mode
has a literal closed-form positivity proof on `x>=5`.

## 4. Exact two-mode margins

Keeping the second mode exactly repairs the origin, where the first mode alone
captures only about eleven percent of `F2(0)`. The two-mode invariants are
rational functions of `x` and `y=e^{-3x}` with positive denominators.

Rational Taylor bounds give

\[
0<y<\frac1{12000}\quad(x\ge\pi),
\]

and, on the short origin band,

\[
\frac1{23000}<y<\frac1{12000}
\quad\left(\frac{157}{50}\le x\le\frac{10}{3}\right).
\]

The exact coefficient checks prove

\[
q_{1,2}>10,\qquad (F_2)_{1,2}>1000,\qquad
(C_4)_{1,2}>50{,}000{,}000.
\tag{4}
\]

The proof of (4) uses three fixed algebraic domains, not a mesh:

- `q`: one bivariate Bernstein rectangle up to `x=10/3`, followed by a
  positive base polynomial minus an exponentially decreasing correction;
- `F2`: a dependent Bernstein band up to `x=10/3`, one rectangle through
  `x=5`, and a positive half-strip Bernstein expansion after `x=5`;
- `C4`: one rectangle up to `x=10/3`, followed by two negative odd-power
  corrections whose ratios to the positive base decrease strictly.

Every Bernstein coefficient is an exact rational number. The verifier checks
361 margin/decay coefficients.

## 5. Modes three and higher

For `t>=27`, exact shifted coefficients prove

\[
0<(-1)^jP_j(t)\le 2^{j+1}t^{j+1},\qquad 0\le j\le6.
\tag{5}
\]

The exact `n=3` term decreases for `x>=3`; its derivative sign is another
positive shifted polynomial. The `n>=4` majorants form a geometric tail.
This gives, on `pi<=x<=5`,

\[
(|e_0|,\ldots,|e_6|)
<\left(7\!\cdot\!10^{-9},4\!\cdot\!10^{-7},2\!\cdot\!10^{-4},
7\!\cdot\!10^{-4},3\!\cdot\!10^{-2},1.1,41\right).
\tag{6}
\]

Exact Bernstein bounds on (1) give

\[
(|a_0|,\ldots,|a_6|)
<(2,5,20,200,2000,60000,1000000).
\tag{7}
\]

Expanding the three raw polynomials with (6)--(7) bounds their changes by

\[
|\Delta N_q|<0.000405,\quad
|\Delta N_{F_2}|<37.959,\quad
|\Delta N_{C_4}|<31{,}549{,}532.
\tag{8}
\]

These are strictly below the two-mode margins in (4).

For `x>=5`, weighted homogeneity removes the need for another compact bound.
The raw weights are `2`, `6`, and `12`, while every tail factor contributes
`e^{-8x}`. Hence every perturbation majorant is decreasing after `x=5`.
Evaluating once at `x=5` gives

\[
|\Delta N_q|<6.49\cdot10^{-11},\quad
|\Delta N_{F_2}|<0.03,\quad
|\Delta N_{C_4}|<418{,}287.
\tag{9}
\]

Again (9) is strictly below (4).

## 6. Candidate conclusion

Equations (3)--(9) prove, subject to audit of this advancement artifact,

\[
q(u)>0,\qquad F_2(u)>0,\qquad \mathcal C_4(u)>0
\quad(u\ge0).
\]

Evenness extends the signs to all real `u`. Combined with the already audited
PF3 sufficiency lemma and PF4 transport identity, this replaces both Arb
compact covers and their analytic tail split. It uses no FLINT, no floating
point, and no interval sweep.

The result is formalizable in a proof assistant: the remaining primitives are
the alternating Machin bound, rational Taylor bounds for exponentials, the
Bernstein positivity lemma, polynomial identities, and geometric-series
estimates. The current SymPy replay is exact but is not itself a Lean/Coq/Isabelle
kernel proof.
