#!/usr/bin/env python3
"""Structural and low-cost certificate regressions."""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

from flint import arb, ctx


HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("compact_certificate", HERE / "certify_compact.py")
CERT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CERT
assert SPEC.loader is not None
SPEC.loader.exec_module(CERT)


class CertificateTests(unittest.TestCase):
    def test_symbol_is_above_mu_past_cutoff(self):
        ctx.prec = 128
        a = arb("0.3")
        z = arb(22)
        arch = CERT.acb(arb(1)/4, z/2).digamma().real - arb.pi().log()
        envelope = 4*(a.sinh()/2 + z*a.cosh())/(z*z + arb(1)/4)
        self.assertGreater((arch-envelope).lower(), 1)

    def test_coarse_full_operator_certificate(self):
        result = CERT.certify("0.0005", 8, 160)
        self.assertGreater(result.lower_bound.lower(), 0)
        self.assertLess(result.operator_upper.upper(), 1)


if __name__ == "__main__":
    unittest.main()

