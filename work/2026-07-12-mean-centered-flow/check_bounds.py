#!/usr/bin/env python3
"""Directed checks for the centered Hilbert--Schmidt flow bound."""

from flint import arb, ctx


ctx.prec=160
pi=arb.pi(); X=arb(2).log(); q=X/pi
linear=(2*(X/2).sinh()+2/pi**2*(2-q)/(1-q)**2)
hs=(arb(4)/3)*arb("0.301")*(arb(8)/3).sqrt()
anchor=arb("0.003702862589668072165872279687848")
endpoint=anchor-arb("0.00368")

print(f"linear_majorant={linear.str(40)}")
print(f"hs_majorant={hs.str(40)}")
print(f"endpoint_lower={endpoint.str(40)}")

if not linear.upper() < (arb(4)/3).lower():
    raise ArithmeticError("linear centered-kernel bound failed")
if not hs.upper() < (arb(2)/3).lower():
    raise ArithmeticError("Hilbert--Schmidt bound failed")
if not endpoint.lower()>0:
    raise ArithmeticError("propagated endpoint failed")
