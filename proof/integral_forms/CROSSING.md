# Closed-form crossing polish

## Original compressed step

The paper differentiates

\[
r(t)=C\frac{z-t}{t-p}
\]

and infers a single density crossing. The differentiation is correct but does
not itself construct the crossing or connect `C` to the actual measures.

## Adopted canonical form

From the normalized densities,

\[
C=\frac{\Lambda}{L\delta}>0,
\qquad
r(t)=\frac{\Lambda(z-t)}{L\delta(t-p)}.
\]

Solving `r(t)=1` before differentiating gives

\[
t_* = \frac{\Lambda z+L\delta p}{\Lambda+L\delta}.
\]

This form is preferred because:

- it constructs rather than postulates the crossing;
- it makes `p<t_*<z` a strict-convex-combination lemma;
- it avoids extended-real endpoint limits for the existence proof;
- it makes the sign test reducible to positive denominator clearing;
- it is inexpensive to formalize in an ordered field.

Indeed,

\[
r(t)-1
=\frac{\Lambda(z-t)-L\delta(t-p)}{L\delta(t-p)}
=\frac{(\Lambda+L\delta)(t_*-t)}{L\delta(t-p)}.
\]

Every denominator factor is positive on `(p,z)`, so

\[
r(t)>1\iff t<t_*,\quad
r(t)=1\iff t=t_*,\quad
r(t)<1\iff t>t_*.
\]

This algebra gives the complete density-difference sign pattern without using
the derivative at all. The derivative remains a useful independent audit:

\[
r'(t)=-\frac{\Lambda(z-p)}{L\delta(t-p)^2}<0.
\]

## Remaining integral step

The strict CDF gap is then most directly written as three positive integral
forms:

\[
\Delta(t)=\int_p^t(f_\mu-f_\nu)>0
\quad (p<t\le t_*),
\]

\[
\Delta(t)=\nu((z,w])-\int_t^z(f_\mu-f_\nu)>0
\quad (t_*\le t<z),
\]

and

\[
\Delta(t)=\nu((t,w])>0
\quad (z\le t<w).
\]

The second formula exposes the strict endpoint mass that the former `Wz`
symbol concealed.

