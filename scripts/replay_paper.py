#!/usr/bin/env python3
"""Non-mutating replay entry point for the PF4 paper evidence.

The maintained proof uses five active certificate boundaries.  The former Arb
compact covers are historical records and are intentionally absent here.
"""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.metadata
import json
from pathlib import Path
import subprocess
import sys


PAPER_CERTIFICATES = (
    "K000005", "K000009", "K000010", "K000011", "K000012"
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


def replay_paper_certificates(root: Path) -> None:
    document = json.loads((root / "mind-data/certificates.json").read_text(encoding="utf-8"))
    certificates = document["items"]
    requirements = {
        requirement
        for certificate_id in PAPER_CERTIFICATES
        for requirement in certificates[certificate_id].get("requirements", [])
    }
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
    root = find_repository()
    replay_paper_certificates(root)
    print("status=paper evidence replay passed")


if __name__ == "__main__":
    main()
