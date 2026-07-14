#!/usr/bin/env python3
"""Regenerate the exact proof-carrying residuals for positive-tail J_b.

This is the deep audit path.  It starts from the 74-term symbolic numerator,
builds the correlated-error left box and mean-value strip blocks, applies only
positive denominator clearings and positive affine/Moebius shifts, and writes
every final integer residual.  The ordinary CERT replay uses the much faster
proof-artifact checker in ``verify_pf4_tail_jb.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import lzma
import os
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / "tmp" / "pf4-tail-jb-cache"
os.environ["MIND_CACHE_DIR"] = str(CACHE)

LEFT_DIR = ROOT / "work/2026-07-13-pf4-jb-separated-transfer"
STRIP_DIR = ROOT / "work/2026-07-14-pf4-jb-meanvalue-right"
sys.path.insert(0, str(LEFT_DIR))
sys.path.insert(0, str(STRIP_DIR))

import prove_jb_blocks_wframe as left  # noqa: E402
import prove_jb_meanvalue_right as strip  # noqa: E402

ARTIFACT = ROOT / "certificates/pf4-tail-jb-residuals.bin.xz"
MANIFEST = ROOT / "scripts/pf4_tail_jb_manifest.json"
MAGIC = b"PF4JB01"


def collapse_error_blocks(blocks, error_count):
    zero = (0,) * error_count
    base = blocks[zero]
    envelope = {}
    for key, numerator in blocks.items():
        if key == zero:
            continue
        for monomial, coefficient in numerator.items():
            envelope[monomial] = envelope.get(monomial, 0) + abs(coefficient)
    return base, envelope


def left_residuals():
    blocks, _, _ = left.build_blocks(False)
    blocks = left.face_divide(blocks)
    base, envelope = collapse_error_blocks(blocks, left.NERR)
    axis = 1
    degree = max(m[axis] for numerator in (base, envelope) for m in numerator)
    transformed = []
    for numerator in (base, envelope):
        work = {
            m: coefficient << (34 * (degree - m[axis]))
            for m, coefficient in numerator.items()
        }
        work = left.shear_axis(work, 1, {(1, 0, 0): 1, (0, 0, 0): 3})
        transformed.append(left.shift_w0(work, left.W_FLOOR))
    keys = set(transformed[0]) | set(transformed[1])
    return {
        monomial: transformed[0].get(monomial, 0) - transformed[1].get(monomial, 0)
        for monomial in keys
    }


def strip_residuals():
    folded = strip.build_blocks()
    s_face = min(min(m[1] for m in total) for _, total, _ in folded.values())
    t_face = min(min(m[2] for m in total) for _, total, _ in folded.values())
    assert s_face >= 2 and t_face >= 1
    folded = {
        key: (
            const,
            {
                (m[0], m[1] - s_face, m[2] - t_face): coefficient
                for m, coefficient in total.items()
            },
            lcd,
        )
        for key, (const, total, lcd) in folded.items()
    }
    items = strip.collapse_classes(folded)
    base = next(numerator for numerator, is_zero in items if is_zero)
    envelope = {}
    for numerator, is_zero in items:
        if is_zero:
            continue
        for monomial, coefficient in numerator.items():
            envelope[monomial] = envelope.get(monomial, 0) + abs(coefficient)
    d2_degree = max(m[2] for numerator in (base, envelope) for m in numerator)
    d1_degree = max(m[1] for numerator in (base, envelope) for m in numerator)
    transformed = []
    for numerator in (base, envelope):
        work = {
            m: coefficient << (34 * (d2_degree - m[2]))
            for m, coefficient in numerator.items()
        }
        work = strip.shear_axis(work, 2, {(1, 0, 0): 1, (0, 0, 0): 3})
        work = strip.strip_substitute(work, d1_degree)
        transformed.append(strip.shift_w0(work, strip.W_FLOOR))
    keys = set(transformed[0]) | set(transformed[1])
    return {
        monomial: transformed[0].get(monomial, 0) - transformed[1].get(monomial, 0)
        for monomial in keys
    }


def source_hashes():
    files = [
        Path("work/2026-07-13-pf4-jb-separated-transfer/prove_jb_blocks_wframe.py"),
        Path("work/2026-07-14-pf4-jb-meanvalue-right/prove_jb_meanvalue_right.py"),
        Path("work/2026-07-13-pf4-six-obligations/density_algebra.py"),
        Path("work/2026-07-13-pf4-jb-collision-radius/prove_jb_collision_radius.py"),
        Path("work/2026-07-13-pf4-jb-separated-transfer/join_positive_tail.py"),
    ]
    return {
        str(path): hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for path in files
    }


def write_artifact(charts):
    metadata = {
        "format": 1,
        "domain": "w0>=43; collision cone or left box or mean-value strip",
        "source_sha256": source_hashes(),
        "charts": {
            name: {
                "count": len(values),
                "zero": sum(value == 0 for value in values.values()),
                "minimum_bits": min(value.bit_length() for value in values.values() if value > 0),
            }
            for name, values in charts.items()
        },
    }
    payload = json.dumps(metadata, sort_keys=True, separators=(",", ":")).encode()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    with lzma.open(ARTIFACT, "wb", preset=6) as handle:
        handle.write(MAGIC)
        handle.write(struct.pack(">I", len(payload)))
        handle.write(payload)
        for name, values in charts.items():
            encoded_name = name.encode()
            handle.write(struct.pack(">B", len(encoded_name)))
            handle.write(encoded_name)
            handle.write(struct.pack(">I", len(values)))
            for monomial, value in sorted(values.items()):
                assert value >= 0, (name, monomial)
                raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
                handle.write(struct.pack(">HHHI", *monomial, len(raw)))
                handle.write(raw)
    digest = hashlib.sha256(ARTIFACT.read_bytes()).hexdigest()
    print(f"artifact={ARTIFACT.relative_to(ROOT)} sha256={digest}")
    print(json.dumps(metadata["charts"], sort_keys=True))
    return digest, metadata


def update_manifest(digest, metadata):
    manifest = json.loads(MANIFEST.read_text())
    manifest["artifact_sha256"] = digest
    manifest["source_sha256"] = metadata["source_sha256"]
    manifest["charts"] = metadata["charts"]
    MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rebuild", action="store_true", help="discard generated caches first")
    args = parser.parse_args()
    if args.rebuild:
        for cache in CACHE.glob("*.pkl"):
            cache.unlink()
    charts = {"left": left_residuals(), "strip": strip_residuals()}
    digest, metadata = write_artifact(charts)
    update_manifest(digest, metadata)
    print("PASS exact positive-tail J_b residual artifact regenerated")


if __name__ == "__main__":
    main()
