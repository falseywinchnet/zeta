# Certified projected-matrix results

## Main runs

All main runs used `N=8`, precision 256 bits, `epsilon=2^-44`, and requested
absolute and relative integration tolerance `2^-180`.

| `a` | pieces | entry perturbation norm | certified smallest projected eigenvalue |
|---:|---:|---:|---:|
| 0.3 | 42 | 3.85948e-23 | `0.0101117508912467834257 +/- 4.75e-23` |
| 0.5 | 43 | 2.11157e-23 | `3.3795155678171590e-6 +/- 4.28e-23` |
| 1.0 | 47 | 2.06736e-23 | `1.4167316571e-12 +/- 4.08e-23` |

Every lower endpoint is positive. These are certified eigenvalue intervals for
the eight-dimensional projected matrices only.

## Independent sensitive-case repeat

The `a=1,N=8` run was repeated at precision 224 bits, `epsilon=2^-40`, and
tolerance `2^-150`:

```text
entry_perturbation_norm = 4.83974685761e-21
eigenvalue_1 = 1.41673166e-12 +/- 7.68e-21
```

It overlaps the tighter main enclosure and retains a positive lower endpoint.

## Low-cost regression certificate

At `a=0.3,N=2`, precision 128, `epsilon=2^-24`, and tolerance `2^-70`:

```text
eigenvalue_1 = 0.011802531109 +/- 5.53e-13
eigenvalue_2 = 0.300384040711 +/- 5.07e-13
```

This configuration is used by the structural test suite.

## Comparison with P000009

The certified centers agree with the prior adaptive computations at `a=0.3`
and `a=0.5`. At `a=1`, the certified center is
`1.4167316571e-12`, while the prior adaptive result was
`1.41653696018e-12`. The prior entrywise quadrature estimate was larger than the
eigenvalue, so that discrepancy is consistent with its explicitly uncertified
status.

## Failures retained

1. No rigorous backend was initially installed. `python-flint==0.9.0` was added
   and pinned for this round.
2. A single interval from the microscopic cutoff to `2` failed Arb's analytic
   validation. A dyadic origin mesh repaired the domain geometry.
3. Arb's nonanalytic range callback requested balls touching zero. Direct Lerch
   evaluation became nonfinite; the proved local magnitude enclosure repaired
   it without weakening analytic checks.
4. Computing `k_i-k_i` from two rounded balls produced a denominator containing
   zero. Mode equality now selects the zero-frequency limit symbolically.
5. An early prototype used a nonexistent `arb.euler`; the correct enclosed
   constant is `arb.const_euler()`.

All failures occurred before the reported main runs.

## Remaining boundary

R112 is met for the tested finite projections: their entries and eigenvalues are
directed enclosures. R113 remains untouched at proof level. The next object is a
lower bound for the form on the orthogonal complement and its coupling to the
certified block.
