#!/usr/bin/env python3
"""Structural checks for the proof-development layer.

This checks document integrity and placeholder policy. It does not check a
mathematical proof and must never be presented as doing so.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent

REQUIRED = (
    "SPECIFICATIONS.MD",
    "README.md",
    "TARGET.md",
    "ROADMAP.md",
    "STATUS.md",
    "TRUSTED_BASE.md",
    "DEPENDENCIES.md",
    "IMPORTS.md",
    "NON_VACUITY.md",
    "CLAIM_INDEX.md",
)

FRAME_IDS = tuple(f"S{i:02d}" for i in range(2, 11))
OBLIGATION_IDS = tuple(f"PO-{i:04d}" for i in range(1, 47))
RECORD_FIELDS = (
    "Frame:",
    "Statement:",
    "Counterexample condition:",
    "Status:",
)


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


for relative in REQUIRED:
    if not (ROOT / relative).is_file():
        fail(f"missing required document: {relative}")

for frame_id in FRAME_IDS:
    if not (ROOT / "frames" / f"{frame_id}.md").is_file():
        fail(f"missing section frame: {frame_id}")

status = (ROOT / "STATUS.md").read_text(encoding="utf-8")
found = re.findall(r"\| (PO-\d{4}) \|", status)
if tuple(found) != OBLIGATION_IDS:
    fail("STATUS.md must list PO-0001 through PO-0046 exactly once in order")

for path in sorted((ROOT / "obligations").glob("PO-*.md")):
    body = path.read_text(encoding="utf-8")
    declared = re.search(r"^# (PO-\d{4})\b", body)
    if declared is None or declared.group(1) != path.stem:
        fail(f"obligation/file identity mismatch: {path.name}")
    for field in RECORD_FIELDS:
        if field not in body:
            fail(f"{path.name} missing record field {field}")

formal_sources = [ROOT / "formal" / "PF4.lean"]
formal_sources.extend(sorted((ROOT / "formal" / "PF4").rglob("*.lean")))
for path in formal_sources:
    if not path.is_file():
        continue
    body = path.read_text(encoding="utf-8")
    for token in ("sorry", "admit"):
        if re.search(rf"\b{token}\b", body):
            fail(f"forbidden Lean placeholder {token!r} in {path.relative_to(ROOT)}")
    if re.search(r"^\s*axiom\s+", body, flags=re.MULTILINE):
        fail(f"undeclared Lean axiom in {path.relative_to(ROOT)}")

print("proof structure: PASS")
print(f"required documents: {len(REQUIRED)}")
print(f"section frames: {len(FRAME_IDS)}")
print(f"status obligations: {len(OBLIGATION_IDS)}")
print(f"expanded obligation records: {len(list((ROOT / 'obligations').glob('PO-*.md')))}")
print("mathematical proof checked by this structural script: NO")
