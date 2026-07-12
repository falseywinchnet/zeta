# Operator normalization notes

Status: raw advancement work. Equation numbers refer to CITE14 unless stated.

## 1. Fourier and convolution conventions

Suzuki uses

\[
\widehat f(z)=\int_{\mathbb R}f(x)e^{izx}\,dx,
\qquad
(f_1*f_2)(x)=\int_{\mathbb R}f_1(y)f_2(x-y)\,dy,
\qquad
\widetilde f(x)=\overline{f(-x)}.
\]

Hence Plancherel has the factor \((2\pi)^{-1}\), and
\(Q_W(v_1,v_2)=W(v_1*\widetilde v_2)\). All computations below are real,
but the Hermitian conjugations must be restored in complex code.

## 2. Continuous screw kernel

For \(u=|t|\), equation (1.3) is

\[
\begin{aligned}
g(t)={}&-4(e^{u/2}+e^{-u/2}-2)
+\sum_{n\le e^u}\frac{\Lambda(n)}{\sqrt n}(u-\log n)\\
&-\frac{u}{2}\bigl(\psi(1/4)-\log\pi\bigr)
-\frac14\left[\Phi(1,2,1/4)
-e^{-u/2}\Phi(e^{-2u},2,1/4)\right].
\end{aligned}
\]

The endpoint terms at \(u=\log n\) vanish. Thus the prime-power ramps are
continuous even though their first derivatives jump. Direct evaluation near zero
has cancellation; the implementation uses high precision for this first version.

Near zero, equation (2.2) decomposes the same function as

\[
g(t)=\tfrac12u\log u+A u
+\sum_{n\le e^u}\frac{\Lambda(n)}{\sqrt n}(u-\log n)+r(t),
\quad
A=\tfrac12(\log(2\pi)+\gamma-1).
\]

For \(u>0\), the smooth remainder can be differentiated as

\[
r''(u)=-2\cosh(u/2)
+\frac{e^{-u/2}}{1-e^{-2u}}-\frac1{2u}.
\]

The removable value at zero is \(r''(0)=-7/4\). This formula follows from
the split \(r=r_0+r_1\) in Section 2.4. It needs a series implementation near
zero to avoid subtraction loss.

## 3. Operators and domains

Embed \(L^2(-a,a)\) into \(L^2(\mathbb R)\) by zero extension and set

\[
L^2_0(-a,a)=\left\{u:\int_{-a}^a u(x)\,dx=0\right\}.
\]

The orthogonal projection is

\[
(P_a u)(x)=1_{(-a,a)}(x)
\left(u(x)-\frac1{2a}\int_{-a}^a u(y)\,dy\right).
\]

Let \(D=i\,d/dx\) with \(D(D)=H^1_0(-a,a)\). Its range is
\(L^2_0(-a,a)\). The adjoint has the same differential expression and domain
\(H^1(-a,a)\). With \(G\) the convolution operator having kernel \(g\),

\[
G_a=P_aGP_a:L^2_0(-a,a)\to L^2_0(-a,a),
\qquad
B_a=D^*G_aD,
\qquad D(B_a)=H^1_0(-a,a).
\]

The projection disappears from the quadratic form because \(Dv\) has mean
zero:

\[
\langle B_av,v\rangle
=\int_{-a}^a\int_{-a}^a
g(x-y)v'(y)\overline{v'(x)}\,dx\,dy.
\]

Theorem 1.1 identifies \(A_a\) as the Friedrichs extension of \(B_a\).
The operator domain \(D(A_a)\) is larger than \(H^1_0(-a,a)\); constants are
an explicit example. Pointwise distribution formulas therefore cannot be used on
all of \(D(A_a)\).

The closed form \(q_a=Q_W^a\) is the form closure of the above core. Its
domain is contained in the logarithmic Fourier space

\[
H^{\log}(-a,a)=\left\{v\in L^2(-a,a):
\int_{\mathbb R}(1+\log^+|z|)|\widehat v(z)|^2\,dz<\infty\right\}.
\]

The paper explicitly warns that the natural finite Gagliardo integral space is
slightly larger than \(D(q_a)\). We therefore do not identify those domains.

## 4. Fixed-interval form

For \(w(t)=v(at)\), equation (4.1) gives

\[
q_a^{(0)}(w)=\frac1a\int_{-1}^1\int_{-1}^1
g(a(x-y))w'(x)\overline{w'(y)}\,dx\,dy,
\]

and its Rayleigh quotient equals that of \(v\). This direct continuous-kernel
formula is the reference implementation.

The independent decomposition uses

\[
L(w)=\frac14\iint\frac{|w(x)-w(y)|^2}{|x-y|}\,dx\,dy
-\frac12\int |w(x)|^2\log(1-x^2)\,dx
\]

and equation (4.5):

\[
q_a^{(0)}(w)=L(w)-[\log a+(2A+1)]\|w\|_2^2
-P_a(w)-a\iint r''(a(x-y))w(y)\overline{w(x)}\,dx\,dy,
\]

where

\[
P_a(w)=2\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}
\Re\int_{-1}^{1-\log(n)/a}
w(t+\log(n)/a)\overline{w(t)}\,dt.
\]

This expression makes every prime-power threshold \(2a=\log n\) explicit.

## 5. Closed-domain nesting and monotonicity

Let \(0<a<b\), and write \(J_{a,b}\) for zero extension from \((-a,a)\)
to \((-b,b)\). On the common core,

\[
Q_W^b(J_{a,b}v)=Q_W^a(v)=Q_W(v),
\qquad
\|J_{a,b}v\|_2=\|v\|_2.
\]

Choose positive form norms

\[
\|v\|_{q_a,c_a}^2=q_a(v)+c_a\|v\|_2^2,
\qquad c_a>-\lambda_a,
\]

and similarly for \(b\). On the common core the squared norms differ by
\((c_b-c_a)\|v\|_2^2\). Each controls the \(L^2\) norm, so they are
equivalent there. If \(v\in D(q_a)\), approximate it in the \(a\)-form norm
by \(v_k\in C_c^\infty(-a,a)\). The zero extensions \(J_{a,b}v_k\) are
Cauchy in the \(b\)-form norm and converge in \(L^2(-b,b)\) to
\(J_{a,b}v\). Closedness yields

\[
J_{a,b}D(q_a)\subset D(q_b),
\qquad q_b(J_{a,b}v)=q_a(v).
\]

Therefore

\[
\lambda_b=\inf_{0\ne w\in D(q_b)}\frac{q_b(w)}{\|w\|_2^2}
\le
\inf_{0\ne v\in D(q_a)}\frac{q_a(v)}{\|v\|_2^2}
=\lambda_a.
\]

This does **not** assert \(D(A_a)\subset D(A_b)\). The nesting belongs to
closed forms under zero extension, which is sufficient for the min--max
statement.

## 6. Numerical epistemics

Using a finite Dirichlet basis gives a conforming subspace of the form core.
Its smallest generalized eigenvalue \(U_{a,N}\) satisfies

\[
\lambda_a\le U_{a,N}.
\]

Increasing nested trial spaces makes \(U_{a,N}\) nonincreasing in exact
arithmetic. No positive value of \(U_{a,N}\) is a lower bound. A negative
Rayleigh quotient, once all numerical and truncation errors are certified,
would be a disproof certificate; positive computations are reconnaissance only.

## 7. Open checks from this normalization

- Verify the removable value and stable series for \(r''\) symbolically and
  numerically.
- Compare the direct kernel matrix with the decomposed form matrix under
  independent quadratures.
- Check basis parity and the small-\(a\) even, simple ground state.
- Determine whether the closed-domain nesting proof needs a citation-level
  lemma about equivalence of lower-bounded form norms in the later refine round.
- Do not infer a lower bound from Galerkin convergence.
