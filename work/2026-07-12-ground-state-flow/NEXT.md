# Next analytic moves

## 1. Instantiate the piecewise flow inequality

On each interval between consecutive `a_n=(log n)/2`, combine:

- the scalar derivative `-1/a`;
- the centered smooth-kernel bound;
- (6) for active prime powers;
- the endpoint-overlap estimate when a new prime power enters.

The established architecture is

`q_b >= (1-eta(a,b))q_a-kappa(a,b)||.||^2`

with explicit arithmetic sums and `eta,kappa ->0` as `b->a`. Reduce `D_a` and
the smooth-flow positive part sharply enough to preserve a useful margin.

## 2. Improve the smooth-flow positive part

The centered Schur estimate is intentionally elementary. Analyze the positive
spectral part of the kernel

`J_a(x-y)=H(a|x-y|)-H(0)`

through its cosine transform or a positive-kernel decomposition. Only that
positive part lowers `q_a`; the large negative rank-one component already helps.

## 3. Develop threshold induction

At `a_n=(log n)/2`, use the endpoint-overlap lemma to add the new prime ramp,
then switch to the active-translation modulus. Determine whether a positive
barrier can be transported across successive thresholds without requiring a
new spectral anchor at each one.

## 4. Maintain the independent route

Keep R83/R88 live: Suzuki's arithmetic `L2` convolution criterion remains the
clean route that does not pass through a shrinking ground-state margin.
