# New trajectories

## 1. Ground-state flow

Scale every form to `(-1,1)` and differentiate its explicit continuous screw
kernel with respect to `a`, piecewise between prime-power breakpoints. Seek a
form inequality for `partial_a q_a`, then a comparison law for `lambda_a`.
The immediate target is an explicit persistence interval grown analytically
from the certified `lambda_0.3` lower bound. The long target is a barrier for the
nonincreasing ground-state curve.

This path uses the strongest secured object already present: the exact kernel,
continuity, domain nesting, and one positive full-operator anchor.

## 2. Arithmetic convolution

Return independently to Suzuki's exact criterion: for every
`0<omega<1/2`, convolution by `h_omega` must send `L2(1,infinity)` into
`L2(0,infinity)`. Rewrite it as a Wiener--Hopf/Hankel mapping problem and seek
an analytic factorization, Hardy-space estimate, or Carleson-measure bound.

This route avoids the vanishing localized spectral margin entirely. Its first
task is to normalize the kernel and isolate the arithmetic term whose mapping
bound is genuinely equivalent to innerness.

## 3. Characteristic-function evolution

Treat the finite-`a` real-rooted characteristic functions as an analytic flow,
not as numerical approximants. First determine the admissible normalization and
the topology of the proposed meromorphic limit. Continue only if the
normalization preserves a zero-controlling analytic class.

## Order

Begin with ground-state flow because it can consume the `a=0.3` theorem
immediately. Run arithmetic convolution as the clean independent route.
Characteristic-function evolution follows after its normalization question is
settled.
