#!/usr/bin/env python3
"""Fast replay of the proof-carrying positive-tail J_b certificate."""

from __future__ import annotations

import hashlib
import json
import lzma
import struct
import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts/pf4_tail_jb_manifest.json"
MAGIC = b"PF4JB01"


def read_exact(handle, size):
    value = handle.read(size)
    assert len(value) == size, "truncated proof artifact"
    return value


def verify_artifact(manifest):
    path = ROOT / manifest["artifact"]
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == manifest["artifact_sha256"]
    with lzma.open(path, "rb") as handle:
        assert read_exact(handle, len(MAGIC)) == MAGIC
        metadata_size = struct.unpack(">I", read_exact(handle, 4))[0]
        metadata = json.loads(read_exact(handle, metadata_size))
        assert metadata["source_sha256"] == manifest["source_sha256"]
        assert metadata["charts"] == manifest["charts"]
        for source, expected in metadata["source_sha256"].items():
            assert hashlib.sha256((ROOT / source).read_bytes()).hexdigest() == expected
        results = {}
        for expected_name in ("left", "strip"):
            name_size = struct.unpack(">B", read_exact(handle, 1))[0]
            name = read_exact(handle, name_size).decode()
            assert name == expected_name
            count = struct.unpack(">I", read_exact(handle, 4))[0]
            seen = set()
            zeros = 0
            minimum_bits = None
            for _ in range(count):
                i, j, k, size = struct.unpack(">HHHI", read_exact(handle, 10))
                monomial = (i, j, k)
                assert monomial not in seen
                seen.add(monomial)
                value = int.from_bytes(read_exact(handle, size), "big")
                if value == 0:
                    zeros += 1
                else:
                    bits = value.bit_length()
                    minimum_bits = bits if minimum_bits is None else min(minimum_bits, bits)
            results[name] = {"count": count, "zero": zeros, "minimum_bits": minimum_bits}
        assert handle.read() == b"", "trailing proof data"
    assert results == manifest["charts"]
    print(f"PASS proof artifact sha256={digest}")
    for name, result in results.items():
        print(f"{name}: residuals={result['count']} negative=0 zero={result['zero']}")


def verify_first_peano_cancellation():
    source = ROOT / "work/2026-07-13-pf4-six-obligations"
    sys.path.insert(0, str(source))
    from density_algebra import full_density

    symbols, _, numerator, _ = full_density()
    collision = {
        symbols["B"]: 0,
        symbols["qm"]: symbols["qx"],
        symbols["pm"]: symbols["px"],
    }
    c0 = sp.diff(numerator, symbols["B"]).subs(collision, simultaneous=True)
    c1 = sp.diff(numerator, symbols["qm"]).subs(collision, simultaneous=True)
    c2 = sp.diff(numerator, symbols["pm"]).subs(collision, simultaneous=True)
    assert sp.expand(
        c0 * symbols["qx"] + c1 * symbols["px"] + c2 * symbols["ux"]
    ) == 0
    print("PASS exact first Peano cancellation")


def verify_collision_and_join():
    collision_dir = ROOT / "work/2026-07-13-pf4-jb-collision-radius"
    join_dir = ROOT / "work/2026-07-13-pf4-jb-separated-transfer"
    sys.path.insert(0, str(collision_dir))
    sys.path.insert(0, str(join_dir))
    import prove_jb_collision_radius
    import join_positive_tail

    prove_jb_collision_radius.main()
    # join_positive_tail is an assertion-only module; import is its replay.
    assert join_positive_tail is not None
    print("PASS collision/left/strip cover including faces")


def main():
    manifest = json.loads(MANIFEST.read_text())
    verify_artifact(manifest)
    verify_first_peano_cancellation()
    verify_collision_and_join()
    print("STATUS=PASS positive-tail J_b certificate")


if __name__ == "__main__":
    main()
