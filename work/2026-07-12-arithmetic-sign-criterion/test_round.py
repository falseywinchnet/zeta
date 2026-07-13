#!/usr/bin/env python3

import importlib.util
import pathlib
import sys
import unittest

import numpy as np


HERE=pathlib.Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location("sign_probe",HERE/"sign_probe.py")
PROBE=importlib.util.module_from_spec(SPEC);sys.modules[SPEC.name]=PROBE
assert SPEC.loader is not None;SPEC.loader.exec_module(PROBE)


class ArithmeticSignTests(unittest.TestCase):
    def test_coefficients_are_positive(self):
        for omega in (0.1,0.25,0.4):
            self.assertTrue(np.all(PROBE.coefficients(omega,1000)[1:]>0))

    def test_kernel_has_both_signs(self):
        grid=np.geomspace(1e-4,0.999,1000)
        for omega in (0.1,0.25,0.4):
            values=PROBE.kernel(omega,grid)
            self.assertLess(values.min(),0)
            self.assertGreater(values.max(),0)


if __name__=="__main__":unittest.main()
