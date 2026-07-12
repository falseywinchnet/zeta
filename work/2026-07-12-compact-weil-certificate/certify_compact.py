#!/usr/bin/env python3
"""Directed certificate for the compact negative part at a=0.3, mu=1.

Let V=(1-m_a)_+ and K be the positive convolution operator with Fourier
multiplier V on L2(-a,a). Then q_a >= I-K.  A normalized Legendre projection P
satisfies

    lambda_max(K) <= lambda_max(P K P) + tr((I-P) K (I-P)).

Both terms are enclosed by Arb interval Riemann sums.  No floating-point value
enters a mathematical bound.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

from flint import acb, acb_mat, arb, arb_mat, ctx


@dataclass
class Certificate:
    matrix: arb_mat
    matrix_top: arb
    perturbation: arb
    tail_trace: arb
    operator_upper: arb
    lower_bound: arb
    cells: int
    active_cells: int
    cutoff_lower: arb
    symbol_lipschitz: arb
    transform_lipschitz: arb


def r0_hat_second(a: arb, z: arb) -> arb:
    numerator = (a.sinh() / 2) * (2 * a * z).cos()
    numerator += z * a.cosh() * (2 * a * z).sin()
    return -4 * numerator / (z * z + arb(1) / 4)


def symbol_point(a: arb, z: arb) -> arb:
    """Exact Arb point enclosure; a=0.3 lies below the first prime threshold."""
    if not ((2 * a).exp().upper() < 2):
        raise ValueError("this certificate assumes no prime-power term")
    arch = acb(arb(1) / 4, z / 2).digamma().real - arb.pi().log()
    return arch - r0_hat_second(a, z)


def symbol_lipschitz(a: arb) -> arb:
    # |d/dz Re psi(1/4+iz/2)| <= psi_1(1/4)/2 from the trigamma series.
    arch = acb(arb(1) / 4).polygamma(1).real / 2
    # Fourier differentiation: |(hat r0'')'| <= integral |t r0''(t)| dt.
    remainder = 16 * a * a.sinh() - 16 * a.cosh() + 16
    return (arch + remainder).upper()


def spherical_j(n: int, x: arb) -> arb:
    """spherical j_n through 0F1, stable at small point arguments."""
    b = arb(n) + arb(3) / 2
    coefficient = arb.pi().sqrt() * x**n / (arb(2) ** (n + 1) * b.gamma())
    return coefficient * (-x * x / 4).hypgeom_0f1(b)


def transform_amplitude(a: arb, n: int, z: arb) -> arb:
    # Integral of the normalized Legendre mode; the omitted phase is i^n.
    return (2 * a * (2 * n + 1)).sqrt() * spherical_j(n, a * z)


def interval_from_endpoints(lower: arb, upper: arb) -> arb:
    if lower.lower() > upper.upper():
        raise ValueError("reversed interval")
    midpoint = (lower.lower() + upper.upper()) / 2
    radius = ((upper.upper() - lower.lower()) / 2).upper()
    return arb(midpoint, radius)


def positive_part(mu: arb, value: arb) -> arb:
    if value.lower() >= mu.upper():
        return arb(0)
    if value.upper() <= mu.lower():
        return mu - value
    return interval_from_endpoints(arb(0), mu - value.lower())


def top_eigenvalue(matrix: arb_mat) -> tuple[arb, arb]:
    n = matrix.nrows()
    midpoint = arb_mat(n, n)
    row_radii = []
    for i in range(n):
        radius = arb(0)
        for j in range(n):
            midpoint[i, j] = matrix[i, j].mid()
            radius += matrix[i, j].rad()
        row_radii.append(radius)
    perturbation = max(row_radii).upper()
    values = acb_mat(midpoint).eig(algorithm="rump")
    values.sort(key=lambda value: float(value.real.mid()))
    top = values[-1].real + arb(0, perturbation)
    return top, perturbation


def certify(step_text: str = "0.00025", modes: int = 8, precision: int = 192) -> Certificate:
    ctx.prec = precision
    a = arb("0.3")
    mu = arb(1)
    cutoff = arb(22)
    step = arb(step_text)
    count_ball = cutoff / step
    cells = int(round(float(count_ball.mid())))
    if not count_ball.contains(cells):
        raise ValueError("cutoff/step must contain the intended integer")
    half = step / 2
    lm = symbol_lipschitz(a)
    # |T_n'(z)| <= ||x||_2 ||phi_n||_2 on (-a,a).
    lt = (2 * a**3 / 3).sqrt().upper()

    matrix = arb_mat(modes, modes)
    tail = arb(0)
    active_cells = 0
    for index in range(cells):
        z = (arb(index) + arb(1) / 2) * step
        m = symbol_point(a, z) + arb(0, (lm * half).upper())
        v = positive_part(mu, m)
        if v.is_zero():
            continue
        active_cells += 1
        amplitudes = []
        for n in range(modes):
            point = transform_amplitude(a, n, z)
            amplitudes.append(point + arb(0, (lt * half).upper()))

        factor = step / arb.pi()
        for i in range(modes):
            for j in range(i, modes):
                if (i - j) % 2:
                    continue
                sign = -1 if ((j - i) // 2) % 2 else 1
                matrix[i, j] += factor * v * sign * amplitudes[i] * amplitudes[j]
                if i != j:
                    matrix[j, i] = matrix[i, j]

        represented = arb(0)
        for amplitude in amplitudes:
            represented += amplitude * amplitude
        complement = 2 * a - represented
        complement_upper = max(arb(0), complement.upper())
        tail += factor * v.upper() * complement_upper

    # For z>=22, Re psi(1/4+iz/2) is increasing by its positive-term series
    # derivative. The absolute r0 transform is bounded by a decreasing envelope.
    z0 = cutoff
    arch0 = acb(arb(1) / 4, z0 / 2).digamma().real - arb.pi().log()
    r_envelope = 4 * (a.sinh() / 2 + z0 * a.cosh()) / (z0 * z0 + arb(1) / 4)
    cutoff_lower = arch0 - r_envelope
    if not (cutoff_lower.lower() > mu.upper()):
        raise ArithmeticError("frequency cutoff positivity was not certified")

    top, perturbation = top_eigenvalue(matrix)
    operator_upper = top.upper() + tail.upper()
    lower_bound = mu - operator_upper
    if not (lower_bound.lower() > 0):
        raise ArithmeticError("compact-operator upper bound did not prove positivity")
    return Certificate(
        matrix=matrix,
        matrix_top=top,
        perturbation=perturbation,
        tail_trace=tail,
        operator_upper=operator_upper,
        lower_bound=lower_bound,
        cells=cells,
        active_cells=active_cells,
        cutoff_lower=cutoff_lower,
        symbol_lipschitz=lm,
        transform_lipschitz=lt,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--step", default="0.00025")
    parser.add_argument("--modes", type=int, default=8)
    parser.add_argument("--precision", type=int, default=192)
    args = parser.parse_args()
    result = certify(args.step, args.modes, args.precision)
    print(
        f"status=certified a=0.3 mu=1 modes={args.modes} cells={result.cells} "
        f"active_cells={result.active_cells} precision={args.precision} step={args.step}"
    )
    print(f"symbol_lipschitz={result.symbol_lipschitz.str(30)}")
    print(f"transform_lipschitz={result.transform_lipschitz.str(30)}")
    print(f"cutoff_symbol_lower={result.cutoff_lower.str(30)}")
    print(f"matrix_top={result.matrix_top.str(40)}")
    print(f"matrix_radius_norm={result.perturbation.str(30)}")
    print(f"legendre_tail_trace={result.tail_trace.str(40)}")
    print(f"operator_norm_upper={result.operator_upper.str(40)}")
    print(f"localized_weil_lower_bound={result.lower_bound.str(40)}")


if __name__ == "__main__":
    main()
