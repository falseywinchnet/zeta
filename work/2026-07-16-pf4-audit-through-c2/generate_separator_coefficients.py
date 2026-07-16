#!/usr/bin/env python3
"""Generate the printable exact positive certificate for the separator C4 numerator."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import sympy as sp


OUTPUT_DIR = Path(__file__).parent / "candidate-paper" / "manuscript" / "generated"


def central_determinant() -> tuple[sp.Poly, tuple[sp.Symbol, ...]]:
    ell2, ell3, ell4, ell5, ell6 = sp.symbols("ell2:7")
    moments = [
        1,
        0,
        ell2,
        ell3,
        ell4 + 3 * ell2**2,
        ell5 + 10 * ell2 * ell3,
        ell6 + 15 * ell2 * ell4 + 10 * ell3**2 + 15 * ell2**3,
    ]
    determinant = sp.Matrix(4, 4, lambda i, j: moments[i + j]).det().expand()
    variables = (ell2, ell3, ell4, ell5, ell6)
    return sp.Poly(determinant, *variables, domain=sp.QQ), variables


def coefficients() -> tuple[int, list[int]]:
    t = sp.symbols("t")
    epsilon = sp.Rational(1, 32)
    p = sp.Poly(2 + 10 * t + 23 * t**2 + 30 * t**3 + 23 * t**4 + 10 * t**5 + 2 * t**6, t)
    derivative = p.diff()
    euler_t = sp.Poly(t, t, domain=sp.QQ)
    numerators = {1: euler_t * derivative}
    for order in range(1, 6):
        numerators[order + 1] = euler_t * (
            numerators[order].diff() * p - order * numerators[order] * derivative
        )
    jets = {2: -epsilon * p**2 + epsilon**2 * numerators[2]}
    for order in range(3, 7):
        jets[order] = epsilon**order * numerators[order]

    determinant, _ = central_determinant()
    numerator = sp.Poly(0, t, domain=sp.QQ)
    for powers, coefficient in determinant.terms():
        term = sp.Poly(coefficient, t, domain=sp.QQ)
        weight = 0
        for index, power in enumerate(powers):
            order = index + 2
            term *= jets[order] ** power
            weight += order * power
        if weight != 12:
            raise ArithmeticError(f"unexpected derivative weight {weight}")
        numerator += term

    rational = list(reversed(numerator.all_coeffs()))
    scale = int(sp.ilcm(*[coefficient.q for coefficient in rational]))
    integers = [int(coefficient * scale) for coefficient in rational]
    if len(integers) != 73 or integers != list(reversed(integers)) or min(integers) <= 0:
        raise ArithmeticError("separator coefficient certificate failed")
    return scale, integers


def write_outputs(scale: int, values: list[int]) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    record = {"schema": 1, "scale": scale, "degree": 72, "coefficients": values}
    encoded = json.dumps(record, indent=2, sort_keys=True).encode("ascii") + b"\n"
    (OUTPUT_DIR / "separator-coefficients.json").write_bytes(encoded)

    rows = [
        "\\begin{center}",
        "\\tiny",
        "\\begin{tabular}{@{}r r@{\\qquad}r r@{}}",
        "\\toprule",
        "$j$ & $a_j$ & $j$ & $a_j$ \\\\",
        "\\midrule",
    ]
    for index in range(19):
        other = index + 19
        right = f"{other} & ${values[other]}$" if other < 37 else "&"
        rows.append(f"{index} & ${values[index]}$ & {right} \\\\")
    rows.extend(["\\bottomrule", "\\end{tabular}", "\\end{center}"])
    (OUTPUT_DIR / "separator-coefficients.tex").write_text("\n".join(rows) + "\n", encoding="ascii")
    print(f"scale={scale} degree=72 independent_coefficients=37 minimum={min(values)}")
    print(f"json_sha256={hashlib.sha256(encoded).hexdigest()}")


def main() -> None:
    write_outputs(*coefficients())


if __name__ == "__main__":
    main()
