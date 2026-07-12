#!/usr/bin/env python3
"""Structural and low-cost certification tests."""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

from flint import arb, ctx


HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("certified_weil_matrix", HERE / "certified_matrix.py")
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class CertifiedMatrixTests(unittest.TestCase):
    def test_prime_power_detection(self):
        observed = dict(MODULE.prime_powers_through(16))
        self.assertEqual(observed, {2: 2, 3: 3, 4: 2, 5: 5, 7: 7, 8: 2, 9: 3, 11: 11, 13: 13, 16: 2})

    def test_origin_radius_decreases_with_cutoff(self):
        ctx.prec = 128
        c = MODULE.constants()
        coarse = MODULE.origin_radius(arb("0.5"), arb(2) ** -20, 4, 4, c)
        fine = MODULE.origin_radius(arb("0.5"), arb(2) ** -30, 4, 4, c)
        self.assertTrue(fine.upper() < coarse.lower())

    def test_low_cost_projected_matrix_is_certified_positive(self):
        result = MODULE.matrix_enclosure(
            "0.3", modes=2, precision=128, epsilon_bits=24, tolerance_bits=70
        )
        self.assertTrue(result.matrix[0, 1].is_zero())
        eigenvalues, perturbation = MODULE.eigenvalue_enclosures(result)
        self.assertTrue(perturbation.lower() > 0)
        self.assertTrue(eigenvalues[0].lower() > 0)
        self.assertTrue(eigenvalues[1].lower() > eigenvalues[0].upper())


if __name__ == "__main__":
    unittest.main()
