# A continuous strict-PF4 separator

Status: raw advancement mathematics.  This note is not an established MIND
factoid until a later refine round audits the argument and certificate.

## Kernel

Let

\[
 (b_{-3},\ldots,b_3)=(2,10,23,30,23,10,2),\qquad c={1\over64},
\]

and put

\[
 B(w)=\sum_{k=-3}^3b_kw^k,
 \qquad
 f(x)=e^{-cx^2}B(e^{2cx}).
\]

Equivalently,

\[
 f(x)=\sum_{k=-3}^3 b_k e^{ck^2}e^{-c(x-k)^2}.
\]

Thus `f` is positive, even, smooth, and Schwartz.  The coefficients are the
autocorrelation of `(1,3,4,2)`, but the proof below does not transfer total
positivity from that discrete sequence.  It proves PF3 and PF4 directly.

## Curvature proof of PF3

For each real `x`, give `K in {-3,...,3}` the tilted probability law

\[
 \Pr_x(K=k)={b_ke^{2ckx}\over B(e^{2cx})}.
\]

Write `kappa_j(x)` for its cumulants and `V=kappa_2`.  Differentiating the
log-partition function gives

\[
 q:=-(\log f)''=2c-(2c)^2V,
 \quad q'=-(2c)^3\kappa_3,
 \quad q''=-(2c)^4\kappa_4.
\]

Because `K` lies in an interval of length six, Popoviciu's inequality gives
`0 <= V <= 9`.  Hence

\[
 q\ge 2c(1-18c)=2c\,{23\over32}>0.
\]

The pointwise PF3 sufficiency quantity from R141 is

\[
 F_2=q^3-\{q q''-(q')^2\}
     =q^3+q(2c)^4\kappa_4+(2c)^6\kappa_3^2.
\]

The fourth cumulant satisfies

\[
 \kappa_4=\mathbb E[(K-\mathbb EK)^4]-3V^2\ge-3V^2\ge-243.
\]

Dropping the nonnegative last term therefore yields

\[
 F_2\ge q\{q^2-3888c^4\}.
\]

At `c=1/64`,

\[
 q^2\ge {529\over256}c^2,
 \qquad
 3888c^4={243\over256}c^2,
\]

so

\[
 F_2\ge q\,{286\over256}c^2>0.
\]

The already-derived global slope lemma R141 now applies: `q>0` and `F2>0`
force every translation minor through order three to be positive for strictly
ordered, noncolliding coordinates.  Consequently `f` is strict PF3.

## Exact PF4 density

Put `epsilon=2c=1/32`, `t=e^{epsilon x}`, and

\[
 P(t)=t^3B(t)=2+10t+23t^2+30t^3+23t^4+10t^5+2t^6.
\]

For the Euler derivative `E=t d/dt`, define integer polynomials `N_j` by

\[
 N_1=tP',\qquad N_{j+1}=t(N_j'P-jN_jP').
\]

Induction gives `E^j log(P)=N_j/P^j`.  Writing
`ell_j=(log f)^(j)`, the cumulants needed by the order-four confluent
invariant are

\[
 \ell_2={-\epsilon P^2+\epsilon^2N_2\over P^2},
 \qquad
 \ell_j={\epsilon^jN_j\over P^j}\quad(3\le j\le6).
\]

Substitution into the audited division-free formula gives

\[
\begin{aligned}
C_4={}&12\ell_2^6+24\ell_2^4\ell_4-24\ell_2^3\ell_3^2
+2\ell_2^3\ell_6-12\ell_2^2\ell_3\ell_5+7\ell_2^2\ell_4^2\\
&+12\ell_2\ell_3^2\ell_4+\ell_2\ell_4\ell_6-\ell_2\ell_5^2
-9\ell_3^4-\ell_3^2\ell_6+2\ell_3\ell_4\ell_5-\ell_4^3
={H(t)\over P(t)^{12}}.
\end{aligned}
\]

Exact rational polynomial arithmetic in `verify_pf4_separator.py` proves
that `H` is palindromic of degree 72 and all 73 coefficients are strictly
positive.  Thus `C4(x)>0` for every real `x`.

The exact PF4 crossing-kernel identity derived in CERT9 is generic for a
positive smooth strictly log-concave kernel.  PF3 gives

\[
 \kappa=2-Q''={2q^3-F_1\over q^3}={q^3+F_2\over q^3}>0,
\]

and the transport density is `D=C4/(Q^6 kappa^2)>0`.  The crossing weight is
positive on every nondegenerate three-point interval, so the identity gives
`partial_xi Psi<0` globally.  The quotient-Wronskian equivalence then proves
that `f` is strict PF4.

## Nonreal Fourier zeros

With the convention `hat f(z)=integral f(x) exp(-izx) dx`, Gaussian
translation gives

\[
 \widehat f(z)=\sqrt{\pi/c}\,e^{-z^2/(4c)}
       \sum_{k=-3}^3b_ke^{ck^2}e^{-ikz}.
\]

Put `w=e^{-iz}` and `u=w+w^{-1}`.  The Laurent factor is zero exactly when

\[
 R_c(u)=2e^{9c}u^3+10e^{4c}u^2
 +(23e^c-6e^{9c})u+(30-20e^{4c})
\]

is zero.  Directed Arb evaluation at `c=1/64` proves that the discriminant of
this real cubic is strictly negative.  Hence `R_c` has a nonreal conjugate
pair.  For `|w|=1`, however, `w+w^{-1}` is real.  Each nonreal root of `R_c`
therefore lifts to roots `w` off the unit circle, and then to Fourier zeros
`z` with nonzero imaginary part.  The Gaussian factor has no zeros.

Thus this one explicit positive even Schwartz kernel is strict PF4 while its
entire Fourier transform has nonreal zeros.  Continuous PF3 and continuous
PF4 membership are each insufficient for Fourier real-rootedness.

## Remaining edge

The separator rules out finite-order total positivity through order four as
the missing Fourier invariant.  It does not identify the additional
geometric, spectral, or arithmetic property that distinguishes the Riemann
kernel.  The pair-score correlation geometry and the shape of the positive
PF4 transport measure are now the relevant comparison axes.
