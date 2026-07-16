#!/usr/bin/env python3
"""Replay the promoted exact-rational origin PF5 certificate."""

from pathlib import Path
import runpy


VERIFIER = (
    Path(__file__).resolve().parents[1]
    / "work"
    / "2026-07-16-rainstar-pf5-witness"
    / "verify_origin_pf5.py"
)

if not VERIFIER.is_file():
    raise SystemExit(f"missing promoted verifier artifact: {VERIFIER}")

runpy.run_path(str(VERIFIER), run_name="__main__")
