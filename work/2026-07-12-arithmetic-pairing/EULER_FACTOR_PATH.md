# Complete Euler-factor path

## Local factors

The coefficient Dirichlet series factors as

`zeta(s-omega)/zeta(s+omega)`

`=product_p (1-p^(-s-omega))/(1-p^(-s+omega))`.

For each prime, the positive coefficient sequence is

`1, p^omega-p^(-omega), p^(2omega)-1, ...`,

or, for `k>=1`, `p^(komega)(1-p^(-2omega))`.

On logarithmic coordinates, each Euler factor is a discrete convolution by
shifts `k log p`. A prime-by-prime proof would need the combined factors up to
the active scale to move the unique sign change past the evaluation point.

## Missing variation theorem

The local generating function is

`(1-p^(-omega)z)/(1-p^omega z)`.

Its numerator has the wrong sign for the standard Pólya-frequency generating
form. Therefore ordinary variation-diminishing convolution does not apply to an
individual Euler factor. In fact its coefficient sequence already fails PF2:
if `b_0=1` and

`b_k=(1-p^(-2omega))p^(komega)` for `k>=1`, then

`b_1^2<b_0 b_2`.

Thus the local sequence is not log-concave. This agrees with the finite-prime
failure theorem.

The remaining candidate is a collective Euler-product theorem: after including
all primes up to the active scale, the combined multiplicative convolution
would have to satisfy a one-sided sign-transfer inequality even though its
individual factors do not.

## Supermultiplicative resource and sharing

The coefficients obey

`c_omega(mn)>=c_omega(m)c_omega(n)`.

This supplies positive weight on high multiples of every negative low index.
But a high integer is a multiple of many low indices. Dividing its resource
among all factorizations introduces divisor multiplicity; no uniform bound
survives for highly composite indices. A valid allocation must exploit more
than supermultiplicativity, or choose a canonical factorization with a proved
global coverage theorem.

## Concrete theorem target

Construct nonnegative allocation weights `a_x(n,m)` such that

1. `a_x(n,m)=0` unless `n<y_omega x` and `y_omega x<nm<=x`;
2. for every low `n`, allocated positive value covers
   `c_omega(n)|G_omega(n/x)|`;
3. for every high `q`, the sum over factorizations `q=nm` consumes at most
   `c_omega(q)G_omega(q/x)`.

Existence of these weights proves the dominance inequality. Finite-prime and
unshared-multiple constructions do not satisfy conditions 2 and 3 together.
