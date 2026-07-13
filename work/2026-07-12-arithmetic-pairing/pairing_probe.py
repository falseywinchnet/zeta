#!/usr/bin/env python3
"""Test finite-prime-chain packets for Suzuki's one-crossing kernel."""

from __future__ import annotations

import importlib.util
import pathlib
import sys

import numpy as np


HERE=pathlib.Path(__file__).resolve().parent
SOURCE=HERE.parent/"2026-07-12-arithmetic-sign-criterion"/"sign_probe.py"
SPEC=importlib.util.spec_from_file_location("sign_probe",SOURCE)
PROBE=importlib.util.module_from_spec(SPEC);sys.modules[SPEC.name]=PROBE
assert SPEC.loader is not None;SPEC.loader.exec_module(PROBE)


def dyadic_packet(omega: float,y: float) -> float:
    levels=int(np.floor(np.log2(1/y)+1e-12))
    value=float(PROBE.kernel(omega,np.array([y]))[0])
    if levels:
        k=np.arange(1,levels+1)
        value+=(1-2**(-2*omega))*float(np.sum(
            2**(k*omega)*PROBE.kernel(omega,2**k*y)
        ))
    return value


def main() -> None:
    for omega in (0.05,0.1,0.25,0.4,0.49):
        print(f"omega={omega}")
        for y in (1e-2,1e-3,1e-4,1e-5,1e-6,1e-7):
            print(f"y={y:.0e} packet={dyadic_packet(omega,y):.12g}")


if __name__=="__main__":main()
