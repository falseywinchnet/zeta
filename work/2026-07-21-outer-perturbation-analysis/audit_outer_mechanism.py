#!/usr/bin/env python3
"""Exact audit of the unscaled weighted outer perturbation mechanism."""
from fractions import Fraction
import importlib.util, os
from pathlib import Path

os.environ["SYMPY_GROUND_TYPES"] = "python"
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "core", ROOT / "scripts/verify_riemann_signs_core.py")
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
sp = c.sp

# 1. A previously implicit elementary envelope is valid already at s=5.
for j, polynomial in enumerate(c.P):
    C = c.ENVELOPE[j]
    for sign in (-1, 1):
        shifted = sp.Poly(sp.expand(
            C*c.x**(j+1) + sign*polynomial).subs(c.x, c.z+5), c.z)
        assert all(value >= 0 for value in shifted.all_coeffs())

# 2. The second mode costs less than another copy of the first envelope.
assert 4**8 < 3_000_000
# For x>=5: exp(-3x)<1/3e6, j<=6, hence 4^(j+2)y<1;
# x<=2x-3 then gives |a_j|<2*C_j*x^j.

# 3. The complete n>=3 tail is geometric after its first term.
# Its successive ratio is at most (4/3)^16 exp(-35)<1/2.
assert c.exp_lower(Fraction(35)) > 2*Fraction(4, 3)**16

# 4. Every cleared polynomial is weighted homogeneous, and every expanded
# perturbation coefficient after absolute values is nonnegative.
weights = {"q": (c.raw_q, 2), "F2": (c.raw_f2, 6), "C4": (c.raw_h4, 12)}
r = sp.symbols("r", nonnegative=True)
alpha = [sp.Rational(2*c.ENVELOPE[j]) for j in range(7)]
beta = [sp.Rational(2*c.ENVELOPE[j]*3**(2*j+4)) for j in range(7)]
budget_polynomials = {}
for name, (poly, weight) in weights.items():
    budget = 0
    for powers, coefficient in sp.Poly(poly, c.RAW).terms():
        assert sum(j*power for j, power in enumerate(powers)) == weight
        high = sp.prod((alpha[j]+beta[j]*r)**power
                       for j, power in enumerate(powers))
        low = sp.prod(alpha[j]**power
                      for j, power in enumerate(powers))
        budget += abs(coefficient)*(high-low)
    budget = sp.Poly(sp.expand(budget), r)
    assert budget.coeff_monomial(1) == 0
    assert all(coefficient >= 0 for coefficient in budget.all_coeffs())
    assert all(weight < 40*k for k in range(1, budget.degree()+1)
               if budget.coeff_monomial(r**k) != 0)
    budget_polynomials[name] = budget

# Thus every x^weight*r^k term has negative derivative on x>=5.
# Use exp(-40)<1/(2e17) only at the endpoint.
assert c.exp_lower(Fraction(40)) > 200_000_000_000_000_000
r0 = sp.Rational(1, 200_000_000_000_000_000)
margins = {"q": 10, "F2": 1000, "C4": 50_000_000}
for name, (_, weight) in weights.items():
    endpoint = sp.Rational(5)**weight * budget_polynomials[name].eval(r0)
    assert endpoint < margins[name]
    print(f"{name}: weight={weight}, budget_degree={budget_polynomials[name].degree()}, "
          f"endpoint={endpoint}, margin={margins[name]}")

# 5. Recheck the independent exact two-mode half-line margins.  The historical
# verifier states them first for logarithmic invariants; a0>1 transfers those
# margins to cleared numerators.  Better: the direct cleared q/C4 numerators
# also satisfy the same decreasing-correction certificate.
normalized = [sp.cancel(
    (p+4*c.y*p.subs(c.x, 4*c.x))/(2*c.x-3)) for p in c.P]
substitution = dict(zip(c.RAW, normalized))
assert sp.factor(normalized[0]-1) == 4*c.y*(8*c.x-3)/(2*c.x-3)
direct_outer = {}
for name, raw, margin in (
    ("q", c.raw_q, 10), ("C4", c.raw_h4, 50_000_000)):
    shifted = c.numerator(sp.cancel(raw.subs(substitution)-margin))
    direct_outer[name] = c.decaying_negative(
        shifted, c.X_SPLIT, 12000)
print("invariant margins", c.certify_two_mode_margins())
print("direct cleared outer margins", direct_outer)
print("PASS universal unscaled outer mechanism")
