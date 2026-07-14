#!/usr/bin/env python3
"""Join lemma: collision cone + two separated boxes cover the positive tail.

Coordinates: a = U-1 >= 0, c = V-1 >= 0, radial coordinate rho = UV-1 =
a + c + ac. P000041 certifies the cleared full-theta J_b numerator is
positive on the collision cone 0 < rho <= 2*eps0 (the all-order radius eps0,
both angular faces included). This round certifies it on the two separated
boxes a >= 2^-34 (left) and c >= 2^-34 (right), each with the opposite gap
free, X >= 23, correlated theta errors.

Cover: if rho >= 2^-32 then not both a,c < 2^-34, since
a + c + ac < 2^-34 + 2^-34 + 2^-68 < 2^-32. And 2*eps0 > 2^-32. So every
configuration with rho > 0 lies in the cone or in a box. rho = 0 is the
exact collision point, where the comparison vanishes identically (C = 0 and
coincident jets) and J_b >= 0 holds by the certified collision data (R158).
"""

from fractions import Fraction

EPS0 = Fraction(46077595453125, 343446590091059391889408)
RADIAL = Fraction(1, 2**32)
GAP = Fraction(1, 2**34)

assert 2 * EPS0 > RADIAL, "cone must reach past the radial floor"
assert 2 * GAP + GAP**2 < RADIAL, "boxes must cover the radial complement"
print("PASS join: cone (rho <= 2 eps0) U left box (a >= 2^-34) U right box (c >= 2^-34)")
print("covers every positive-tail configuration with rho = UV-1 > 0")
print(f"  2*eps0 = {float(2*EPS0):.3e} > 2^-32 = {float(RADIAL):.3e}")
print(f"  2*gap + gap^2 = {float(2*GAP + GAP**2):.3e} < 2^-32")
