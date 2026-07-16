# Global PF3 certificate for the Riemann kernel

For the even Riemann/de Bruijn-Newman kernel

`Phi(u) = sum_{n>=1} (4 pi^2 n^4 e^{9|u|/2} - 6 pi n^2 e^{5|u|/2}) e^{-pi n^2 e^{2|u|}}`

write `ell = log Phi`, `s = ell'`, `q = -ell'' > 0`, `F1 = q q'' - (q')^2`,
`F2 = q^3 - F1`. The claim certified here is that `Phi` is globally PF3: every
translation-kernel minor `det[Phi(x_i - y_j)]` of order at most three is
nonnegative for strictly increasing tuples.

## Chain

1. Orders one and two. Every theta term is positive because
   `2 pi n^2 e^{2|u|} >= 2 pi > 3`, so `Phi > 0`; and `q > 0` is strict
   log-concavity, which is exactly order two.

2. Reduction. Dividing the three columns by the middle translate turns
   order-three nonnegativity into convexity of the planar curve
   `(B, A) = (Phi(t-b)/Phi(t), Phi(t+a)/Phi(t))`, equivalently
   `L(t,a,b) = d/dt log(B'/(-A')) >= 0` for all real `t` and `a, b > 0`.

3. Sufficiency lemma. `L = int_{t-b}^{t+a} q + M(t-b,t) - M(t,t+a)` where
   `M(alpha,beta)` is the `q`-weighted mean of `q'/q`. Bounding the means by
   endpoint extremes of `q'/q` and its derivative `F1/q^2` gives
   `L >= int_{t-b}^{t+a} min(q^3, F2)/q^2`. Hence `q > 0` and `F2 >= 0`
   pointwise on `R` imply global PF3, uniformly over interior, collision, and
   escape configurations.

4. Compact core. `certify_pf3_curvature.py` proves by directed interval
   arithmetic (python-flint/Arb, precision 192, termwise theta tails, 7731
   adaptive cells with second-order Taylor enclosures) that on `[0,1]`:
   `q >= 18.726`, `F1 >= 0.181`, `F2 >= 3889.2`. Evenness of `q`, `F1`, `F2`
   extends this to `[-1,1]`. Output: `pf3-curvature-certificate.txt`.

   This 192-bit, 7731-cell base cover is distinct from
   `scripts/verify_pf3_reduction.py`. The latter is a quick audit wrapper: its
   imported Arb jet comparison uses 256 bits and its mpmath diagnostics use
   40--60 decimal digits. `scripts/replay_paper.py --full` executes the base
   cover first and then the wrapper, checking both registered output hashes.

5. Tail. For `|u| >= 1`, with `x = pi e^{2u} >= pi e^2 > 23.14`, explicit
   enclosures of the log-correction `w = log(1+rho)` of the dominant theta
   term give `|q-4x| <= 19.8/x`, `|qdot-8x| <= 176/x`, `|qddot-16x| <= 2082/x`,
   hence `q >= 4x - 0.86 > 0`, `|F1| <= 11596`, and
   `F2 >= (4x-0.86)^3 - 11596 > 7.5e5 > 0`. The `64x^2` leading terms of
   `q qddot` and `qdot^2` cancel exactly; `F2` compares `O(1)` against
   `O(x^3)`, so no delicate cancellation is required.

Conclusion: `q > 0` and `F2 > 0` on all of `R`, so the Riemann kernel is
globally PF3. This certificate does not by itself address PF4 or PF5. The
current exact-order classification is recorded separately in R145, with the
order-five boundary supplied by CERT11.

## Audit

`scripts/verify_pf3_reduction.py` (this refine round) verifies independently:

- sympy symbolic identity of the slope criterion `L` with
  `d/dt log(B'/(-A'))`;
- sympy symbolic identity of every log-derivative expansion `ell_2..ell_6`
  used by the certificate jet, of `F1' = q q''' - q' q''`,
  `F1'' = q q'''' - (q'')^2`, `F2'`, `F2''`, of the theta-term derivative
  recursion `P_{j+1} = (5/2 - 2x) P_j + 2x P_j'`, and of the tail operator
  algebra for `q`, `qdot`, `qddot` in `w`-derivatives including the exact
  constant cancellations;
- an independent mpmath series implementation reproducing the certificate jet
  `(q, q', q'', q''', q'''', F1, F2)` to machine zero at sampled points;
- the sufficiency chain `L >= int min(q^3,F2)/q^2 > 0` numerically on sampled
  `(t,a,b)` including near-collision configurations;
- the intermediate tail constants `|w^(k)| <= {1.61, 3.33, 10.4, 42.8}/x^{k+1}`
  at sampled `x >= pi e^2` (tight within 1% at the boundary).

`verify_tail_bounds.py` (in the round directory) checks every final tail
inequality against the exact series with directed rounding on a grid
`u in [1, 6]`, using u-local tail majorants; output `tail-bounds-check.txt`
also confirms the true asymptotics `q = 4x + 6/x + O(x^{-2})`, `F1 -> 384`.

Uniform theta-tail majorants in the certificate are valid on `[0,1]` because
each omitted-term bound is decreasing in `e^{2u}` once `pi n^2 > deg + 5/4`,
which holds from the first omitted index `n = 8`.

The interval helper drops no radii: python-flint `arb(mid, rad)` adds the
midpoint ball's own radius, and consecutive cells share exact ball endpoints,
so the certified cells cover `[0, 1]`.

## Epistemic status

The interval computations are machine-certified with directed rounding. The
reduction, sufficiency lemma, and tail enclosures are analytic derivations
produced inside this repository (P000023) and audited symbolically and
numerically in this refine round; they are not published literature. Khare's
Theorem E (papers/khare-multiply-positive.pdf) independently implies that
order-three minor nonnegativity plus measurability and decay already yields
TN3, so the separate order-one and order-two checks are a redundancy, not a
gap.

Evidence retained with the round: Sobol scans of unrestricted order-3 and
order-4 configurations (2^20 each, no negative minor) and a 2^22-sample scan
of the slope criterion (no negative value; floor at the collision boundary
where the sufficiency bound degenerates to zero, as predicted).
