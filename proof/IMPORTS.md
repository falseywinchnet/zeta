# Imported mathematics ledger

This ledger separates theorem-bearing imports from background citations. A
local PDF and checksum establish evidence identity, not theorem correctness.

## I-001 — Jacobi theta transformation

Required statement: for `x > 0`,
`ϑ(x) = x^(-1/2) ϑ(1/x)` for the exact theta normalization in T0.

Used by: S02 even continuation.

Current source: de Bruijn is cited for the kernel normalization, but the paper
does not give a precise theorem locator for the theta transformation.

Status: `OBLIGATION`. The maintained `PF4.Theta`, `PF4.KernelSeries`, and
`PF4.Kernel` modules deliberately do not import a Jacobi-theta theorem,
Fourier transform, Poisson summation, or complex analysis. The transformation
is still needed if parity transports positive-side certificates to the full
line. A future proof must either expose a transparent real derivation of that
statement or replace parity by direct all-real estimates; renaming an
equivalent Poisson theorem does not close this import.

## I-002 — local uniform convergence and differentiation of theta series

Required statement: the defining theta series and the finite derivative family
needed through order nine converge locally uniformly after the substitutions
used in the PF4 and PF5 paths.

Used by: S02, S03, S10.

Status: `FORMAL_FRAGMENT`. `PF4.KernelSeries` proves a literal six-level
derivative tower on every interval `(-1,B)`, hence at every `t ≥ 0`, using
finite polynomial coefficient bounds and polynomial-times-exponential
comparison series. No special-function integration theorem is used. The
all-real statement and its connection to parity remain open.

## I-003 — determinant and matrix integration facts

Required statements: determinant multilinearity, row operations, finite sums
commuting with integrals, and the fundamental theorem of calculus under the
regularity used in the iterated quotient identity.

Used by: S05.

Status: `OBLIGATION`; expected mathlib imports, exact declaration names unset.

## I-004 — extrema and weighted means on compact intervals

Required statements: a continuous function on `[a,b]` attains extrema; a
positive-weight average lies between its extrema; the positive-part derivative
bound controls endpoint variation.

Used by: S04.

Status: `OBLIGATION`; expected mathlib imports plus local lemmas.

## I-005 — probability/CDF integration by parts

Required statement: for the compactly supported absolutely continuous measures
constructed in S08, the expectation difference of an absolutely continuous
function with derivative `D` equals the integral of the CDF difference against
`D`, with correct orientation and zero boundary term.

Used by: S09.

Status: `OBLIGATION`. Prefer a direct compact-interval proof specialized to the
explicit densities; this minimizes measure-theory trust and endpoint ambiguity.

## I-006 — strict integral positivity

Required statement: a continuous nonnegative integrand that is strictly
positive on a nonempty open subinterval has strictly positive integral.

Used by: S04, S06, S09, S10.

Status: `OBLIGATION`; expected mathlib theorem or short local proof.

## Background-only sources

- Schoenberg, Karlin, Belton–Guillot–Khare–Putinar: definitions and historical
  PF context. Their transform characterization is not used to prove T1–T3.
- Khare: finite-order context, not a proof dependency of T1–T3.
- de Bruijn: historical kernel normalization; may become theorem-bearing only
  if I-001 is sourced there with an exact locator.
- Dimitrov–Xu, Csordas–Varga, Gröchenig, Michałowski: context/comparison. The
  direct witness T2 avoids importing Michałowski's numerical result.

## Closure rule

For every theorem-bearing import, add exact source version, theorem number or
page, hypotheses, local substitution, formal-library declaration if any, and
the dependencies used in its proof. Continue until the branch reaches a formal
theorem, a locally reconstructed proof, or a visible unresolved leaf.
