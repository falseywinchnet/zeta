# Next advancement boundary

The generic actual-coordinate cascade is now closed conditionally on three
explicit kernel inequalities:

```text
q > 0,
F2 = q^3 - (q*q2 - q1^2) > 0,
kernelDeterminantC4(q,q1,q2,q3,q4) > 0.
```

The next advancement should instantiate `Phi` with the literal even Riemann
kernel already represented by repository evidence, derive its differentiation
tower without an opaque smoothness premise, and attack these three inequalities
in increasing order of jet depth.  The order should be:

1. identify the exact maintained kernel object and its domain;
2. close derivative-under-sum/integral identities for `Phi1` through `Phi3` and
   for `q1` through `q4`;
3. prove `Phi > 0` and `q > 0` from the literal representation;
4. reduce `F2 > 0` to the simplest available closed integral or moment form;
5. reduce `det C4 > 0` to its non-vacuous strict moment/determinant statement;
6. instantiate `terminalQuotD_pos_of_actualCoordinateCascade` and connect that
   concrete terminal sign to the maintained finite-column cascade.

Do not replace any of the three inequalities by a hypothesis equivalent to the
desired terminal sign.  Each must be proved from the literal kernel
representation or an independently replayable theorem chain.
