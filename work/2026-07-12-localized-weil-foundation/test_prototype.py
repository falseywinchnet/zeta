#!/usr/bin/env python3
"""Structural tests for the raw localized-Weil prototype."""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

import numpy as np
from scipy import integrate


HERE = pathlib.Path(__file__).resolve().parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


operator = load("round_weil_operator", "weil_operator.py")
spectral = load("round_spectral_crosscheck", "spectral_crosscheck.py")


class PrototypeTests(unittest.TestCase):
    def test_von_mangoldt_prime_powers(self):
        table = operator.von_mangoldt_table(10)
        expected = {
            2: np.log(2),
            3: np.log(3),
            4: np.log(2),
            5: np.log(5),
            7: np.log(7),
            8: np.log(2),
            9: np.log(3),
        }
        self.assertEqual(set(np.flatnonzero(table)), set(expected))
        for n, value in expected.items():
            self.assertAlmostEqual(table[n], value, places=14)

    def test_screw_kernel_is_even_and_zero_at_origin(self):
        x = np.array([-1.1, -0.3, 0.0, 0.3, 1.1])
        values = operator.screw_g(x, dps=35)
        self.assertEqual(values[2], 0.0)
        np.testing.assert_allclose(values, values[::-1], rtol=0, atol=1e-14)

    def test_remainder_second_matches_pointwise_second_difference(self):
        def remainder(u: float) -> float:
            full = float(operator.screw_g(u, dps=45))
            table = operator.von_mangoldt_table(int(np.floor(np.exp(u) + 1e-12)))
            prime = sum(
                table[n] / np.sqrt(n) * (u - np.log(n))
                for n in np.flatnonzero(table)
            )
            return full - 0.5 * u * np.log(u) - operator.A_CONST * u - prime

        for u in (0.1, 0.5, 1.2):
            h = 1e-4
            finite_difference = (remainder(u + h) - 2 * remainder(u) + remainder(u - h)) / h**2
            self.assertAlmostEqual(
                finite_difference, float(operator.remainder_second(u)), delta=8e-7
            )

    def test_analytic_basis_transform(self):
        omega = np.array([0.2, 3.7])
        transforms = spectral.interval_transform(omega, 4)
        for row, value in enumerate(omega):
            for mode in range(1, 5):
                numeric_real = integrate.quad(
                    lambda x: np.sin(mode * np.pi * (x + 1) / 2) * np.cos(value * x),
                    -1,
                    1,
                    epsabs=1e-13,
                )[0]
                numeric_imag = integrate.quad(
                    lambda x: np.sin(mode * np.pi * (x + 1) / 2) * np.sin(value * x),
                    -1,
                    1,
                    epsabs=1e-13,
                )[0]
                self.assertAlmostEqual(transforms[row, mode - 1].real, numeric_real, places=12)
                self.assertAlmostEqual(transforms[row, mode - 1].imag, numeric_imag, places=12)

    def test_derivative_correlation_reduction(self):
        for t, left, right in ((0.0, 1, 1), (0.3, 2, 3), (1.2, 4, 1)):
            numeric = integrate.quad(
                lambda y: (
                    left
                    * np.pi
                    / 2
                    * np.cos(left * np.pi * (y + t + 1) / 2)
                    * right
                    * np.pi
                    / 2
                    * np.cos(right * np.pi * (y + 1) / 2)
                ),
                -1,
                1 - t,
                epsabs=1e-13,
            )[0]
            self.assertAlmostEqual(
                operator._derivative_correlation(t, left, right), numeric, places=12
            )

    def test_independent_forms_agree_before_first_prime_threshold(self):
        direct = operator.direct_ritz(0.2, modes=4, grid=240, dps=35)
        decomposed = operator.decomposed_ritz(0.2, modes=4, quadrature=180)
        np.testing.assert_allclose(
            direct.eigenvalues[:4], decomposed.eigenvalues[:4], rtol=0, atol=2.5e-3
        )


if __name__ == "__main__":
    unittest.main()
