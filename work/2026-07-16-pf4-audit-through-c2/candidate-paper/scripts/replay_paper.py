#!/usr/bin/env python3
"""Non-mutating replay entry point for the PF4 paper evidence.

Quick mode executes the six certificate-facing paper verifiers and checks their
registered output hashes. Full mode first reruns the two theorem-producing
192-bit directed compact covers and checks their retained output hashes.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import subprocess
import sys


PAPER_CERTIFICATES = (
    "K000002", "K000003", "K000005", "K000009", "K000010", "K000011"
)

FULL_COVERS = (
    {
        "label": "PF3 compact cover (7731 cells)",
        "directory": "work/2026-07-12-riemann-kernel-pf34-classification",
        "script": "certify_pf3_curvature.py",
        "stdout_sha256": "a52a360cdc5e0a616d791e038d759952af287c85b9f22bfa4e3bba39373c827f",
    },
    {
        "label": "C4 compact cover (8050 cells)",
        "directory": "work/2026-07-13-riemann-kernel-pf4-verification",
        "script": "certify_c4.py",
        "stdout_sha256": "bf2436a454ece2c4ef97917f0aa606f29a7e3c401faa9428c203893a7f52d0cc",
    },
)


def find_repository() -> Path:
    for directory in Path(__file__).resolve().parents:
        if (directory / "mind-data/certificates.json").is_file():
            return directory
    raise SystemExit("could not locate the repository root")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_requirements(requirements: set[str]) -> None:
    for requirement in sorted(requirements):
        package, expected = requirement.split("==", 1)
        observed = importlib.metadata.version(package)
        if observed != expected:
            raise SystemExit(
                f"requirement mismatch: {package}=={expected} required, {observed} installed"
            )


def run_checked(label: str, argv: list[str], cwd: Path, stdout_hash: str, stderr_hash: str) -> str:
    result = subprocess.run(argv, cwd=cwd, capture_output=True, check=False)
    if result.returncode:
        sys.stderr.buffer.write(result.stderr)
        raise SystemExit(f"{label}: exited {result.returncode}")
    observed_stdout = sha256(result.stdout)
    observed_stderr = sha256(result.stderr)
    if observed_stdout != stdout_hash or observed_stderr != stderr_hash:
        raise SystemExit(
            f"{label}: output mismatch\n"
            f"  stdout expected {stdout_hash}, observed {observed_stdout}\n"
            f"  stderr expected {stderr_hash}, observed {observed_stderr}"
        )
    return f"PASS {label} stdout={observed_stdout}"


def replay_full_covers(root: Path) -> None:
    empty_hash = sha256(b"")
    for task in FULL_COVERS:
        directory = root / task["directory"]
        print(run_checked(
            task["label"],
            [sys.executable, task["script"]],
            directory,
            task["stdout_sha256"],
            empty_hash,
        ))


def replay_paper_certificates(root: Path) -> None:
    document = json.loads((root / "mind-data/certificates.json").read_text(encoding="utf-8"))
    certificates = document["items"]
    requirements = {
        requirement
        for certificate_id in PAPER_CERTIFICATES
        for requirement in certificates[certificate_id].get("requirements", [])
    }
    # The C4 wrapper is lightweight, but its theorem-producing base cover uses Arb.
    requirements.add("python-flint==0.9.0")
    check_requirements(requirements)
    tasks = []
    for certificate_id in PAPER_CERTIFICATES:
        item = certificates[certificate_id]
        argv = [sys.executable if value == "{python}" else value for value in item["runner"]["argv"]]
        tasks.append((
            f"CERT{int(certificate_id[1:])}",
            argv,
            root,
            item["runner"]["stdout_sha256"],
            item["runner"]["stderr_sha256"],
        ))
    with ThreadPoolExecutor(max_workers=min(4, len(tasks))) as executor:
        for message in executor.map(lambda task: run_checked(*task), tasks):
            print(message)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--full",
        action="store_true",
        help="rerun the 7731- and 8050-cell directed compact covers before the quick audits",
    )
    args = parser.parse_args()
    root = find_repository()
    if args.full:
        replay_full_covers(root)
    replay_paper_certificates(root)
    print("status=full paper replay passed" if args.full else "status=quick paper audit passed")


if __name__ == "__main__":
    main()
