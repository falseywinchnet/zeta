# PF4 Wronskian-reduction certificate

Status: refine-round proof audit of P000027. This note certifies the W3 theorem
and the reduction of global PF4 to one three-point inequality. It does **not**
certify that inequality or global PF4.

## Definitions and hypotheses

Let `f` be a positive sufficiently smooth translation kernel and write

\[
s=(\log f)',\qquad q=-s'.
\]

For `a<b`, define

\[
A(a,b)=s(a)-s(b),\qquad
M(a,b)=\frac{q(b)-q(a)}{A(a,b)},\qquad
N(a,b)=\frac{q'(b)-q'(a)}{A(a,b)}.
\]

For `xi<m<r`, define

\[
\Lambda(\xi;m,r)=A(\xi,r)+M(\xi,m)-M(m,r),
\qquad
\Psi(\xi;m,r)=\Lambda+T\log\Lambda,
\]

where `T` translates all arguments together. For the Riemann kernel `Phi`,
CERT2 supplies `q>0`, `F2>0`, and the strict positivity of the R141 functional
`Lambda` on its full domain.

## Generic quotient and integral machinery

For ordered translates `u_j(t)=f(t-y_j)`, put

\[
v_j=(u_j/u_1)',\qquad w_j=(v_j/v_2)'.
\]

Direct differentiation gives

\[
W(u_1,u_2,u_3)=u_1^3W(v_2,v_3),
\]

\[
W(u_1,u_2,u_3,u_4)=u_1^4v_2^3w_3^2
\frac{d}{dt}\left(\frac{w_4}{w_3}\right),
\]

with the analogous order-two quotient identities. These identities hold for
arbitrary differentiable functions wherever the displayed quotients exist.

After dividing the columns by `u_1(t_i)`, bottom-up consecutive row
differences reduce the collocation determinant to a determinant of increments.
The fundamental theorem of calculus and determinant multilinearity then give,
for `k=3,4`,

\[
\det[U_j(t_i)]_{i,j=1}^k
=\int_{t_1}^{t_2}\!\cdots\!\int_{t_{k-1}}^{t_k}
\det[U'_{j+1}(\tau_i)]_{i,j=1}^{k-1}\,d\tau_1\cdots d\tau_{k-1},
\]

where `U_1=1`. Thus pointwise positivity of the successive quotient
Wronskians implies positivity of the corresponding global collocation minors.
The verifier checks these statements with generic SymPy functions, not a
finite polynomial sample.

## W3 theorem

For `p_3<p_2<p_1`, direct generic differentiation and exact mean splitting
give

\[
L_3=T\log(v_3/v_2)
=\frac{A(p_3,p_2)}{A(p_3,p_1)}
\Lambda(p_3;p_2,p_1).
\]

For `Phi`, `q>0` makes both `A` factors positive and CERT2 makes `Lambda`
strictly positive. Hence every translate Wronskian `W_3` is strictly positive.
The generic iterated-integral identity then recovers strict global order-three
minors without invoking an external extended-Chebyshev theorem.

## Order-four reduction

For `j=3,4`, let `g_j=T log(v_j/v_2)`. Generic calculus gives

\[
L_4=T\log(w_4/w_3)
=\Delta_{4,3}[g+T\log g].
\]

Writing `A=A(p_2,p_1)` and applying exact mean splitting gives

\[
g_j+M(p_j,p_2)-M(p_j,p_1)=\Lambda_j-A,
\]

and therefore

\[
L_4=\Psi(p_4;p_2,p_1)-\Psi(p_3;p_2,p_1).
\]

Since `p_4<p_3<p_2<p_1` range freely and the lower-order factors are strictly
positive, global PF4 for `Phi` is equivalent to

\[
\partial_\xi\Psi(\xi;m,r)\le 0
\quad\text{for every }\xi<m<r.
\]

Strict inequality implies strict TP4. Conversely PF4 gives nonnegative
confluent order-four Wronskians, hence the displayed monotonicity.

## Evidence boundary

`scripts/verify_pf4_wronskian_reduction.py` checks:

1. all quotient identities for generic functions;
2. the `k=3,4` iterated-integral identities for generic functions by exact
   symbolic integration;
3. translation derivatives and every mean-splitting identity;
4. the generic L3 formula and factored generic L4 assembly;
5. the closed forms for `Lambda_xi`, `T Lambda`, `dxi T Lambda`, and
   `dxi Psi`;
6. the exact map from `Lambda` to R141;
7. two independent 50-digit spot-checks on `Phi`.

The 8.4-million-point scan in P000027 remains numerical progress only. Neither
the scan nor this certificate proves `partial_xi Psi<=0` globally.
