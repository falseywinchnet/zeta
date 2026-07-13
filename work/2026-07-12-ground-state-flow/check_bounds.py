#!/usr/bin/env python3
"""Directed arithmetic checks for the pre-prime flow constants."""

from flint import arb, ctx


ctx.prec = 160
pi = arb.pi()
x = arb(2).log()
q = x/pi
majorant = (
    2*((x/2).cosh()-1)
    + x*(x/2).sinh()
    + 2/pi*((1-q)**-2-1)
)
lambda_03 = arb("0.003702862589668072165872279687848")
log_upper = arb(7)/3750
linear = (arb(13)/4)*arb(7)/12500
endpoint = lambda_03-log_upper-linear
beta = 2/pi-arb.const_euler()

print(f"X={x.str(40)}")
print(f"H_majorant={majorant.str(40)}")
print(f"four_times_H={ (4*majorant).str(40) }")
print(f"endpoint_lower={endpoint.str(40)}")
print(f"log_energy_beta={beta.str(40)}")

if not majorant.upper() < (arb(13)/16).lower():
    raise ArithmeticError("centered H majorant did not fit below 13/16")
if not endpoint.lower() > 0:
    raise ArithmeticError("propagated endpoint was not positive")
if not beta.lower() > 0:
    raise ArithmeticError("logarithmic-energy beta was not positive")
