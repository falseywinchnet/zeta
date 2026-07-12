#!/usr/bin/env python3
"""Regression tests for the raw Fourier-symbol prototypes."""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

import numpy as np
from scipy import linalg


HERE = pathlib.Path(__file__).resolve().parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


SYMBOL = load("round_symbol", "symbol_probe.py")
RELATIVE = load("round_relative", "relative_compact_probe.py")


class SymbolTests(unittest.TestCase):
    def test_even(self):
        z = np.array([0.0, 0.2, 3.0, 18.5, 200.0])
        np.testing.assert_allclose(SYMBOL.symbol(1.0, z), SYMBOL.symbol(1.0, -z))

    def test_r0_transform_sign_recovers_certified_centers(self):
        expected = {0.3: 0.0101117508912468, 0.5: 3.379515567817159e-6,
                    1.0: 1.4167316571e-12}
        for a, target in expected.items():
            _, qmat = RELATIVE.matrices(a, 8, 2000.0, 0.5, 16)
            observed = linalg.eigvalsh(qmat)[0]
            self.assertLess(abs(observed-target), max(5e-6*abs(target), 5e-17))

    def test_high_frequency_growth(self):
        self.assertGreater(float(SYMBOL.symbol(1.0, 5000.0)), 0.0)


if __name__ == "__main__":
    unittest.main()
