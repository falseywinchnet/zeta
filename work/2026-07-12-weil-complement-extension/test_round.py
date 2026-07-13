#!/usr/bin/env python3
"""Fast structural tests for the complement-extension round."""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

from flint import arb, ctx


HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("certify_a05", HERE / "certify_a05.py")
CERT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CERT
assert SPEC.loader is not None
SPEC.loader.exec_module(CERT)


class RoundTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 96

    def test_cutoff(self):
        a = arb("0.5")
        cutoff = arb(130)
        arch = (CERT.acb(1)/4+CERT.I*cutoff/2).digamma().real-arb.pi().log()
        prime = 2*arb(2).log()/arb(2).sqrt()
        remainder = 4*(a.sinh()/2+cutoff*a.cosh())/(cutoff**2+arb(1)/4)
        self.assertGreater((arch-prime-remainder).lower(), arb(2).upper())

    def test_completeness_partial_sum_below_total(self):
        a = arb("0.5")
        for z in (arb("0.25"), arb(3), arb(20)):
            partial = sum((CERT.amplitude(a, n, z)**2 for n in range(40)), CERT.acb(0))
            self.assertLessEqual(partial.real.lower(), (2*a).upper())

    def test_parity_zero(self):
        self.assertEqual(CERT.integrate_entry(arb("0.5"), arb(2), 0, 1, [], arb("1e-20")), arb(0))


if __name__ == "__main__":
    unittest.main()
