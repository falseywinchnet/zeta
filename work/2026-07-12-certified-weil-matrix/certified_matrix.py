#!/usr/bin/env python3
"""Directed ball enclosures for finite localized-Weil Ritz matrices.

The integration backend is Arb through python-flint.  The origin is removed
from numerical integration and enclosed analytically.  Every remaining interval
is split at prime-power ramps so that the callback is analytic on each piece.

This certifies a finite projected matrix only.  It does not lower-bound the full
localized-Weil operator.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

from flint import acb, acb_mat, arb, arb_mat, ctx


def prime_power_base(n: int) -> int | None:
    """Return p if n is a positive power of the prime p, else None."""
    if n < 2:
        return None
    for p in range(2, int(math.isqrt(n)) + 1):
        if n % p:
            continue
        # p must itself be prime.
        if any(p % q == 0 for q in range(2, int(math.isqrt(p)) + 1)):
            return None
        value = n
        while value % p == 0:
            value //= p
        return p if value == 1 else None
    return n  # n is prime


def prime_powers_through(limit: int) -> list[tuple[int, int]]:
    return [(n, p) for n in range(2, limit + 1) if (p := prime_power_base(n))]


@dataclass(frozen=True)
class Constants:
    quarter: arb
    pi: arb
    psi_quarter: arb
    phi_one: acb
    A: arb


def constants() -> Constants:
    quarter = arb(1) / 4
    pi = arb.pi()
    return Constants(
        quarter=quarter,
        pi=pi,
        psi_quarter=quarter.digamma(),
        phi_one=acb(1).lerch_phi(2, quarter),
        A=(arb(2).log() + pi.log() + arb.const_euler() - 1) / 2,
    )


def archimedean_g(u: acb, c: Constants, analytic: bool) -> acb:
    """The non-prime part of Suzuki (1.3), valid for Re(u)>0."""
    if analytic and not (u.real.lower() > 0):
        return acb("nan")
    z = (-2 * u).exp()
    return (
        -4 * ((u / 2).exp() + (-u / 2).exp() - 2)
        - (u / 2) * (c.psi_quarter - c.pi.log())
        - c.quarter
        * (c.phi_one - (-u / 2).exp() * z.lerch_phi(2, c.quarter))
    )


def full_g_piece(
    u: acb,
    active: tuple[tuple[arb, arb], ...],
    c: Constants,
    analytic: bool,
) -> acb:
    # Arb's validated integrator may request a coarse real range evaluation on
    # a ball wider than the integration interval. If that ball touches zero,
    # the Lerch formula is undefined termwise although g is continuous. Supply
    # a rigorous local magnitude enclosure instead; analytic evaluations still
    # reject neighborhoods crossing the branch.
    if not analytic and not (u.real.lower() > 0):
        if not u.imag.contains(0):
            return acb("nan")
        upper = abs(u.real).upper()
        if upper.is_zero():
            return acb(0)
        if not (upper < 1):
            return acb("nan")
        magnitude = (upper / 2) * (-upper.log()) + c.A * upper + arb(3) * upper**2 / 2
        for log_n, weight in active:
            magnitude += weight * (upper + abs(log_n))
        return acb(arb(0, magnitude.upper()))
    value = archimedean_g(u, c, analytic)
    if not value.is_finite():
        return value
    for log_n, weight in active:
        value += weight * (u - log_n)
    return value


def derivative_correlation(t: acb, left_mode: int, right_mode: int, c: Constants) -> acb:
    """Integral phi_left'(y+t) phi_right'(y) over y in (-1,1-t)."""
    ki = c.pi * left_mode / 2
    kj = c.pi * right_mode / 2
    length = 2 - t

    def oscillatory(frequency: arb, phase: acb, mathematically_zero: bool = False) -> acb:
        if mathematically_zero:
            return length * phase.cos()
        return ((frequency * length + phase).sin() - phase.sin()) / frequency

    return (ki * kj / 2) * (
        oscillatory(ki - kj, ki * t, left_mode == right_mode)
        + oscillatory(ki + kj, ki * t)
    )


def origin_radius(a: arb, epsilon: arb, i: int, j: int, c: Constants) -> arb:
    """Bound the omitted integral on [0,epsilon].

    For 0 <= u <= 1, |r''(u)| < 3.  The proof is recorded in
    CERTIFICATION.md.  Thus |r(u)| <= 3u^2/2.
    """
    if not ((a * epsilon).upper() < 1):
        raise ValueError("origin bound requires a*epsilon < 1")
    if not ((a * epsilon).upper() < arb(2).log()):
        raise ValueError("origin segment must precede the first prime ramp")
    ki = c.pi * i / 2
    kj = c.pi * j / 2
    correlation_bound = 2 * ki * kj
    log_integral = (epsilon**2 / 4) * (-(a * epsilon).log() + arb(1) / 2)
    linear_integral = c.A * epsilon**2 / 2
    remainder_integral = a * epsilon**3 / 2  # 3a/2 * integral(t^2) = a eps^3/2
    return (correlation_bound * (log_integral + linear_integral + remainder_integral)).upper()


@dataclass
class CertifiedMatrix:
    a: arb
    modes: int
    matrix: arb_mat
    max_origin_radius: arb
    max_integration_radius: arb
    pieces: int


def matrix_enclosure(
    a_text: str,
    modes: int,
    precision: int = 256,
    epsilon_bits: int = 40,
    tolerance_bits: int = 180,
) -> CertifiedMatrix:
    ctx.prec = precision
    c = constants()
    a = arb(a_text)
    if not (a.lower() > 0):
        raise ValueError("a must be positive")
    epsilon = arb(2) ** (-epsilon_bits)
    tolerance = arb(2) ** (-tolerance_bits)

    # The integer limit is only combinatorial. Guard it using a high-precision
    # midpoint and reject an interval that could straddle an integer threshold.
    exp_2a = (2 * a).exp()
    if not (exp_2a.upper() < 2**52):
        raise ValueError("prime-power enumeration exceeds exact float integer range")
    lower_limit = int(float(exp_2a.lower().floor()))
    upper_limit = int(float(exp_2a.upper().floor()))
    if lower_limit != upper_limit:
        raise ValueError("a interval straddles a prime-power inclusion threshold")
    powers = prime_powers_through(lower_limit)
    ramps = []
    for n, p in powers:
        log_n = arb(n).log()
        weight = arb(p).log() / arb(n).sqrt()
        ramps.append((log_n / a, log_n, weight, n))

    # A single interval [epsilon, first_ramp] asks Arb to prove analyticity on
    # complex neighborhoods much wider than their distance from the branch at
    # zero. A dyadic mesh keeps every near-origin neighborhood in Re(t)>0.
    near_end = arb("0.125")
    if ramps and ramps[0][0].upper() < near_end.lower():
        near_end = ramps[0][0] / 2
    breakpoints = [epsilon]
    point = epsilon
    while (2 * point).upper() < near_end.lower():
        point *= 2
        breakpoints.append(point)
    if breakpoints[-1].upper() < near_end.lower():
        breakpoints.append(near_end)
    breakpoints.extend(point for point, _, _, _ in ramps)
    breakpoints.append(arb(2))
    active_counts = [0] * (len(breakpoints) - len(ramps) - 1)
    active_counts.extend(range(1, len(ramps) + 1))
    active_counts.append(len(ramps))
    matrix = arb_mat(modes, modes)
    max_origin = arb(0)
    max_integral_radius = arb(0)

    for i in range(1, modes + 1):
        for j in range(i, modes + 1):
            # Mode n is even about zero for odd n and odd for even n. The even
            # convolution kernel preserves parity, so cross-parity entries are
            # mathematically zero; do not replace that identity by interval
            # cancellation.
            if (i - j) % 2:
                matrix[i - 1, j - 1] = 0
                matrix[j - 1, i - 1] = 0
                continue
            total = acb(0)
            for piece, (left, right) in enumerate(zip(breakpoints[:-1], breakpoints[1:])):
                # Active ramps are selected by construction, without comparing
                # approximate breakpoint values. A ramp is active on the piece
                # beginning at its own breakpoint, where it initially vanishes.
                active_count = active_counts[piece]
                frozen = tuple(
                    (log_n, weight)
                    for _, log_n, weight, _ in ramps[:active_count]
                )

                def integrand(t: acb, analytic: bool) -> acb:
                    corr = derivative_correlation(t, i, j, c)
                    corr += derivative_correlation(t, j, i, c)
                    return full_g_piece(a * t, frozen, c, analytic) * corr / a

                value = acb.integral(
                    integrand,
                    left,
                    right,
                    abs_tol=tolerance,
                    rel_tol=tolerance,
                    eval_limit=100000,
                    depth_limit=100,
                )
                if not value.is_finite():
                    raise ArithmeticError(f"integration failed for entry {(i, j)} piece {piece}")
                if not value.imag.contains(0):
                    raise ArithmeticError(f"spurious imaginary exclusion for entry {(i, j)}")
                total += value

            omitted = origin_radius(a, epsilon, i, j, c)
            entry = total.real + arb(0, omitted)
            matrix[i - 1, j - 1] = entry
            matrix[j - 1, i - 1] = entry
            max_origin = max(max_origin, omitted)
            max_integral_radius = max(max_integral_radius, total.real.rad())

    return CertifiedMatrix(
        a=a,
        modes=modes,
        matrix=matrix,
        max_origin_radius=max_origin,
        max_integration_radius=max_integral_radius,
        pieces=len(breakpoints) - 1,
    )


def eigenvalue_enclosures(certified: CertifiedMatrix) -> tuple[list[arb], arb]:
    """Midpoint eigenvalue balls widened by a rigorous interval-matrix norm."""
    matrix = certified.matrix
    n = certified.modes
    midpoint = arb_mat(n, n)
    radius_rows = []
    for i in range(n):
        row_radius = arb(0)
        for j in range(n):
            midpoint[i, j] = matrix[i, j].mid()
            row_radius += matrix[i, j].rad()
        radius_rows.append(row_radius)
    perturbation_norm = max(radius_rows).upper()
    eigenvalues = acb_mat(midpoint).eig(algorithm="rump")
    eigenvalues.sort(key=lambda value: float(value.real.mid()))
    enclosed = []
    for value in eigenvalues:
        if not value.imag.contains(0):
            raise ArithmeticError("midpoint symmetric matrix produced nonreal eigenvalue")
        enclosed.append(value.real + arb(0, perturbation_norm))
    return enclosed, perturbation_norm


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", required=True)
    parser.add_argument("--modes", type=int, default=8)
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--epsilon-bits", type=int, default=40)
    parser.add_argument("--tolerance-bits", type=int, default=180)
    parser.add_argument("--print-matrix", action="store_true")
    args = parser.parse_args()

    result = matrix_enclosure(
        args.a,
        args.modes,
        args.precision,
        args.epsilon_bits,
        args.tolerance_bits,
    )
    eigenvalues, perturbation = eigenvalue_enclosures(result)
    print(
        f"a={result.a} N={result.modes} pieces={result.pieces} "
        f"precision={args.precision} epsilon_bits={args.epsilon_bits} "
        f"tolerance_bits={args.tolerance_bits}"
    )
    print(f"max_origin_radius={result.max_origin_radius.str(20)}")
    print(f"max_integration_radius={result.max_integration_radius.str(20)}")
    print(f"entry_perturbation_norm={perturbation.str(20)}")
    for index, value in enumerate(eigenvalues[: min(5, len(eigenvalues))], 1):
        print(f"eigenvalue_{index}={value.str(40)}")
    if args.print_matrix:
        print(result.matrix)


if __name__ == "__main__":
    main()
