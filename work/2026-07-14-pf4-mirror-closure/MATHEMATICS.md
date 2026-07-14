# Closing the all-negative PF4 mirror

## 1. Why the pointwise `J` reflection was the wrong object

P000050 showed that `J(x;m,r)` is not invariant under

\[
(x,m,r)\mapsto(-r,-m,-x).
\]

The reflected expression controls a right-end derivative of
`Psi_-=lambda-T log lambda`, whereas the target is the left-end derivative of
`Psi_+=lambda+T log lambda`.  This prevents a direct substitution in `J`, but
it does not prevent reflection of the finite order-four determinant from
which the differential criterion came.

## 2. Ordered Wronskian reflection

Let `Phi` be even and let

\[
p_1>p_2>\cdots>p_k.
\]

Define the reflected, order-restored points

\[
q_j=-p_{k+1-j},
\qquad q_1>q_2>\cdots>q_k.
\]

For the translate Wronskian matrix, evenness gives

\[
\Phi^{(i)}(p_j)=(-1)^i\Phi^{(i)}(-p_j).
\]

Passing from the matrix at `p` to the matrix at `q` therefore performs two
operations:

1. it extracts the row sign
   `(-1)^(0+1+...+(k-1))=(-1)^(k(k-1)/2)`;
2. it reverses `k` columns, with the same sign
   `(-1)^(k(k-1)/2)`.

The signs cancel.  Thus, for every order,

\[
\boxed{W_k(p_1,\ldots,p_k)=W_k(q_1,\ldots,q_k).}          \tag{1}
\]

`prove_mirror_closure.py` checks (1) with a generic symbolic matrix through
order four.  In particular, no sign is lost at order four: both factors are
`(-1)^6=+1`.

## 3. Transfer of the finite positive-tail theorem

Put

\[
a_{23}={1\over2}\log(23/\pi)<1.
\]

R162 proves

\[
\partial_x\Psi(x;m,r)\le0
\qquad(a_{23}\le x<m<r).
\]

For four ordered points

\[
p_1>p_2>p_3>p_4\ge a_{23},
\]

CERT5 gives the exact quotient reduction

\[
L_4=\Psi(p_4;p_2,p_1)-\Psi(p_3;p_2,p_1).
\]

The R162 derivative sign makes `L_4>=0`.  All quotient prefactors are positive
by global PF3 and strict `W_3>0`, so the complete finite Wronskian satisfies

\[
W_4(p_1,p_2,p_3,p_4)\ge0.                                \tag{2}
\]

Equation (1) transfers (2) to every four ordered points at or below
`-a_23`.

## 4. Return to the required differential orientation

Take an arbitrary triple

\[
x<m<r<-1
\]

and, for `epsilon>0`, use the four negative points

\[
p_1=r,qquad p_2=m,qquad p_3=x,qquad p_4=x-\epsilon.
\]

They all lie below `-a_23`, because the directed scalar inequality

\[
\pi e^2>23
\]

gives `a_23<1`.  Reflection maps them to four positive ordered points whose
smallest member is `-r>1>a_23`.  Hence (1)--(2) prove the negative finite
Wronskian nonnegative.

Applying CERT5 again in the original negative orientation gives

\[
\Psi(x-\epsilon;m,r)-\Psi(x;m,r)\ge0.
\]

Divide by `epsilon` and let it decrease to zero.  The backward difference has
the exact limit

\[
\lim_{\epsilon\downarrow0}
{\Psi(x-\epsilon;m,r)-\Psi(x;m,r)\over\epsilon}
=-\partial_x\Psi(x;m,r).
\]

Therefore

\[
\boxed{\partial_x\Psi(x;m,r)\le0\qquad(x<m<r<-1).}       \tag{3}
\]

This is the missing all-negative mirror lemma.  It is a determinant theorem,
not an invariance claim about `J`.

## 5. Remaining PF4 domain

P000050 already proves or compactifies every triple with `r>=-1`.  Equation
(3) closes every triple with `r<-1`.  Consequently the only still-unproved
triples are contained in the finite ordered chart

\[
\boxed{-R_{64}<x<m<r<R_{64},
\qquad R_{64}={1\over2}\log(64/\pi).}                    \tag{4}
\]

Some parts of (4) are already covered by the positive tail, escape, and mirror
theorems.  Certifying the whole enlarged chart is sufficient and gives clean
overlap boundaries.

Global PF4 is not yet proved: (4) still needs the origin collision cone, both
angular faces, and its separated compact complement.
