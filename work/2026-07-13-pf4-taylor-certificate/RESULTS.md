# Results by proof obligation

## 1. Division-free jet source: completed

`jet14.py` generates the theta derivative polynomials recursively through
order eighteen, evaluates the complete retained theta sum, and adds a uniform
termwise tail majorant.  Curvature derivatives are then reconstructed through
the exact logarithmic-cumulant recurrence.  Gap quotients are no longer used
inside the Taylor source: endpoint functions are composed from a common local
jet, preserving their dependence.

## 2. Certified compact jets: completed

`certify_compact_jets.py` proves centered Taylor enclosures for
`q,q',...,q^(8)` on 16,384 complete cells covering `[0,1]`.  Evenness of `q`
and forced parity of its derivatives cover `[-1,1]`.  Each cell uses six
centered terms and a directed seventh-order remainder.  The canonical stream
of all cell records has SHA-256

```text
63589c9ba8d3b11b1b528f880eb95ab29ae3ae5415a0d724a442e01e6948bb1b
```

The compact manifest stores the partition, global ranges, precision, theta
truncation, and record hash without committing 52 MB of generated records.

## 3. Dependency-aware Jhat arithmetic: completed as machinery

`tm3.py` implements sparse degree-five multivariate Taylor models on a
normalized three-cube.  Products retain common variables; discarded terms and
input remainders are enclosed explicitly.  Reciprocals are validated from the
directed residual `1-pq`, not assumed from a formal series.

`certify_tm_cells.py` composes `s,q,q',q''` from a common local theta jet and
evaluates the exact `Jhat` expression.  Four complete cells are certified,
including angularly skewed cells and a cell whose `x` chart crosses zero.  At
width `0.002` this succeeds where the previous natural-ball extension needed
width `0.00002`.  These cells validate the machinery; they are not a global
cover.

## 4. Boundary modules: algebra completed; two signs remain

`verify_boundary_modules.py` proves exactly:

```text
rho=0:    Jhat = C4/(12 q^3)
theta=0:  Jhat = E/rho^2
theta=1:  Jhat has a finite 21-term two-point numerator over B q(m) q(x)
```

The radial face is positive by the existing `C4` certificate.  The reflection
chart is implemented using `q(-t)=q(t)` and `s(-t)=-s(t)`, with directed even
and odd Taylor remainders.  Global positivity of the `theta=0` edge `E` and of
the distinct `theta=1` boundary has not been proved.  Treating those faces as
equal by reflection would be an orientation error.

## 5. Analytic compactification: not completed

`audit_compactification.py` proves that the currently available resolved-tail
boxes do not leave a compact residue.  Their successive gaps must be at least
`log(2)/2`, whereas

```text
(x,m,r) = (M-log(2)/4, M, M+log(2)/4)
```

escapes to infinity without entering either resolved-gap box.  The exact
one-theta-term density is positive on this family, but the full-theta
near-collision transfer remains unproved.  Escape asymptotics without a
uniform threshold also do not compactify the domain.

## 6. Compact-core cover: blocked by obligation 5

`cover-manifest.json` records four certified calibration cells and explicitly
sets `global_core_claim` to false.  Since the remaining domain is not known to
be bounded, no finite collection of cells can yet certify the global target.
Generating a large cover under an arbitrary cutoff would be a numerical sweep,
not a proof.

## Mathematical status

No counterexample was found.  Global PF4 is not proved.  The next theorem is
now narrower: obtain a uniform full-theta lower bound for collision-divided
`Jhat` in the same-tail near-collision cone, and separately certify the two
angular boundary functions.  Those results would convert the present partial
covering machinery into a legitimate global certificate engine.
