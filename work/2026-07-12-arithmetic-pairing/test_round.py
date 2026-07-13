#!/usr/bin/env python3

import importlib.util
import pathlib
import sys
import unittest


HERE=pathlib.Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location("pairing_probe",HERE/"pairing_probe.py")
PAIR=importlib.util.module_from_spec(SPEC);sys.modules[SPEC.name]=PAIR
assert SPEC.loader is not None;SPEC.loader.exec_module(PAIR)


class PairingTests(unittest.TestCase):
    def test_dyadic_packet_eventually_negative(self):
        for omega in (0.05,0.1,0.25,0.4,0.49):
            self.assertLess(PAIR.dyadic_packet(omega,1e-7),0)

    def test_local_euler_factor_fails_log_concavity(self):
        for prime in (2,3,5,7):
            for omega in (0.1,0.25,0.4):
                b0=1
                b1=(1-prime**(-2*omega))*prime**omega
                b2=(1-prime**(-2*omega))*prime**(2*omega)
                self.assertLess(b1*b1,b0*b2)


if __name__=="__main__":unittest.main()
