# Hall boundary

For a chosen allocation graph, the max-flow/min-cut theorem says that dominance
follows if and only if every set `A` of negative indices satisfies

`sum_{n in A} c(n)|G(n/x)|`

`<=sum_{q in N(A)} c(q)G(q/x)`,                         (H)

where `N(A)` is the permitted set of positive resource indices.

## Divisibility graph

Taking `n--q` when `n|q` is the strongest immediate use of coefficient
supermultiplicativity. It fails. At `omega=0.25,x=1000`, only about `83.4%` of
negative demand can be met; at `omega=0.4,x=1000`, about `74.3%` can be met.

The minimum cuts contain most composite negative indices. Their neighborhoods
miss high primes and other positive indices having no eligible negative divisor.
Those omitted indices carry substantial positive weight.

## Prime-pool repair

Allowing every negative index to draw from every high prime restores the tested
allocations through `x=1000`. It still fails at `omega=0.4,x=3000`. Adding one
arithmetic class at a time postpones the obstruction rather than proving (H).

## Conclusion

A sufficient pairing graph needs neighborhoods broad enough to capture the
complete second-order coefficient balance, while remaining structured enough
for all Hall inequalities to be proved. Divisibility, finite prime chains, and
an unrestricted prime pool do not meet both requirements.

If every positive index is made available to every negative index, (H) reduces
to the original total dominance inequality. Thus enlarging the graph without a
new arithmetic theorem eventually becomes tautological.
