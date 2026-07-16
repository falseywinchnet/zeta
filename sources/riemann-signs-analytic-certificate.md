# Sweep-free Riemann-kernel sign certificate

Status: refine-round audit and promotion of P000072.

## Claim

For the Riemann kernel, with `ell=log Phi`,

\[
q=-\ell''>0,\qquad
F_2=q^3-\{q q''-(q')^2\}>0,\qquad
\mathcal C_4>0
\]

on the whole real line.  The proof uses exact rational polynomial algebra,
Taylor and geometric-series inequalities, and no interval sweep or
floating-point sign decision.

## Order-three implication

For a positive strictly log-concave kernel, put `s=(log f)'`, `q=-s'`,
`F1=q q''-(q')^2`, and `F2=q^3-F1`. Exact differentiation identifies the
logarithmic slope of the middle-column-normalized order-three minor with

\[
L(t,a,b)=s(t-b)-s(t+a)
+\frac{q(t)-q(t-b)}{s(t-b)-s(t)}
-\frac{q(t+a)-q(t)}{s(t)-s(t+a)}.
\]

Both quotients are `q`-weighted means of `q'/q`. Choosing a minimum on the
left interval and a maximum on the right gives

\[
L(t,a,b)\ge
\int_{t-b}^{t+a}\frac{\min(q^3,F_2)}{q^2}\,du.
\]

Thus `q>0` and `F2>0` imply strict global PF3. The paper prints the complete
weighted-mean argument; the launcher independently checks the generic
logarithmic-slope identity.

## Two-mode normalization

For `u>=0`, put `x=pi exp(2u)`, `y=exp(-3x)`, and

\[
P_0(t)=2t-3,\qquad
P_{j+1}(t)=(5/2-2t)P_j(t)+2tP_j'(t).
\]

After division by the positive first theta mode, the first two normalized
derivatives and the remaining tail are

\[
a_j={P_j(x)+4yP_j(4x)\over P_0(x)},\qquad
e_j=\sum_{n\ge3}{n^2e^{-(n^2-1)x}P_j(n^2x)\over P_0(x)}.
\]

Machin's formula gives `pi>157/50`, so every denominator is positive.

## Cleared invariants

For a raw derivative vector `(a0,...,a6)`, the verifier reconstructs

\[
N_q=a_1^2-a_0a_2,
\]

the degree-six cleared numerator of `F2`, and

\[
N_{C_4}=\det[a_{i+j}]_{i,j=0}^3.
\]

It proves symbolically that division by the positive powers `a0^2`, `a0^6`,
and `a0^4` gives `q`, `F2`, and `C4`.  Independently expanding the central
moment determinant reproduces the thirteen-term cumulant formula.

## Exact two-mode margin

Alternating rational exponential bounds give

\[
0<y<1/12000\quad(x\ge\pi),
\]

and `1/23000<y<1/12000` on `157/50<=x<=10/3`.  Exact Bernstein conversion on
three fixed algebraic domains, followed by decreasing-ratio polynomial
arguments, proves

\[
q_{1,2}>10,\qquad (F_2)_{1,2}>1000,\qquad
(C_4)_{1,2}>50,000,000.
\]

The conversion checks 361 rational coefficients.  There is no point mesh.

## Modes three and higher

For `t>=27` and `0<=j<=6`, shifted coefficient positivity proves

\[
0<(-1)^jP_j(t)\le2^{j+1}t^{j+1}.
\]

The normalized `n=3` term decreases for `x>=3`; its derivative sign is a
positive shifted polynomial.  The successive `n>=4` majorants have ratio
less than `10^-9`.  On `pi<=x<=5` this yields

\[
(|e_0|,\ldots,|e_6|)<
(7\,10^{-9},4\,10^{-7},2\,10^{-4},7\,10^{-4},3\,10^{-2},1.1,41).
\]

Exact Bernstein bounds give

\[
(|a_0|,\ldots,|a_6|)<(2,5,20,200,2000,60000,1000000).
\]

Termwise expansion of the three raw polynomials then gives

\[
|\Delta N_q|<0.000405,\quad
|\Delta N_{F_2}|<37.959,\quad
|\Delta N_{C_4}|<31,549,532.
\]

For `x>=5`, weighted homogeneity and the factor `exp(-8x)` make every
perturbation majorant decreasing.  Its single endpoint evaluation gives

\[
|\Delta N_q|<6.49\,10^{-11},\quad
|\Delta N_{F_2}|<0.03,\quad
|\Delta N_{C_4}|<418,287.
\]

Both sets lie strictly below the two-mode margins.  Evenness extends the
conclusion from `u>=0` to the real line.

## Replay boundary

`scripts/verify_riemann_signs_exact.py` forces SymPy's pure-Python rational
domain, rejects any import whose name begins with `flint`, and runs the
preserved exact verifier from P000072.  The certificate hashes the launcher,
the verifier, its retained output, and this proof record.  Its only external
requirement is SymPy 1.14.0; all sign decisions are exact.
