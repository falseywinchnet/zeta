# Results

## Closed in Lean

`ThetaSeriesJet.lean` contains the following replayable objects and theorems.

1. `thetaMode` is the literal `n >= 1` summand from the paper, with Lean index
   `k` representing `n = k + 1`.
2. `certPoly` implements the CERT12 recurrence
   \(P_{j+1}=(5/2-2X)P_j+2XP'_j\).
3. `thetaModeJet j k t` is the resulting recursive mode.
4. `thetaModeJet_zero_eq_thetaMode` proves that level zero is exactly the paper
   summand, rather than a replacement chosen to make differentiation easy.
5. `hasDerivAt_thetaModeJet` proves
   \(\partial_t\operatorname{mode}_j=\operatorname{mode}_{j+1}\) for every
   natural `j`, hence in particular through level six.
6. `summable_thetaModeJet_zero_at_zero` proves actual convergence at `t = 0`
   using the explicit bound
   \[
   |\operatorname{mode}_0(n,0)|
   \le (4\pi^2+6\pi)n^4e^{-n}.
   \]
7. `summable_exponentialMajorant` proves summability of every comparison series
   \(K_j n^{2j+6}e^{-rn}\) when `r > 0`.
8. `ThetaJetControl.hasDerivAt_seriesJet` applies the locally uniform
   termwise-differentiation theorem using the proved mode recurrence, the proved
   central convergence base, and the supplied norm majorants.
9. `ThetaJetControl.derivativeTowerThroughSix` packages exactly the six ordinary
   derivatives required by the cleared raw-jet bridge on the controlled set.

The final Lean check exited successfully.  The file contains no `sorry`, `admit`,
or custom axiom.

## Why the result is non-vacuous

No hypothesis assumes that the infinite sum has any derivative.  The control
object asks only for an open preconnected set containing zero and explicit
summable upper bounds on the next six mode levels.  Level-zero convergence is a
theorem.  Higher-level convergence follows from the majorants.  Only then does
Lean pass the already-proved summand derivatives through the sum.

## Polynomial trace

The recurrence produces:

```text
P0 = 2*x - 3
P1 = -4*x^2 + 15*x - 15/2
P2 = 8*x^3 - 56*x^2 + 165*x/2 - 75/4
P3 = -16*x^4 + 180*x^3 - 529*x^2 + 1635*x/4 - 375/8
P4 = 32*x^5 - 528*x^4 + 2588*x^3 - 4256*x^2 + 15465*x/8 - 1875/16
P5 = -64*x^6 + 1456*x^5 - 10720*x^4 + 30510*x^3
     - 126121*x^2/4 + 142935*x/16 - 9375/32
P6 = 128*x^7 - 3840*x^6 + 39640*x^5 - 173580*x^4
     + 644791*x^3/2 - 445627*x^2/2 + 1305165*x/32 - 46875/64
```

These expansions are a diagnostic trace only.  The proof uses the recurrence,
which is smaller, general in `j`, and better suited to the interval majorant.

## Unresolved edge

The bounded-interval coefficient inequality in `NEXT.md` is not yet formalized.
Consequently this round does not claim the actual infinite sum has the complete
six-derivative jet without a `ThetaJetControl`.  It has reduced that claim to a
specific polynomial-times-Gaussian estimate and proved every other step of the
transfer mechanism.
