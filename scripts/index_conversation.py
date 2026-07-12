#!/usr/bin/env python3
"""Losslessly split a ChatGPT text export into prompt/response records."""

import argparse
import hashlib
import json
import re
from pathlib import Path


HEADER = re.compile(r"^## (Prompt|Response):\s*$", re.MULTILINE)


def parse(text):
    markers = list(HEADER.finditer(text))
    preamble = text[: markers[0].start()] if markers else text
    records = []
    for index, match in enumerate(markers):
        end = markers[index + 1].start() if index + 1 < len(markers) else len(text)
        body = text[match.end():end]
        body = body[1:] if body.startswith("\n") else body
        records.append({"sequence": index + 1, "role": match.group(1).lower(), "body": body})
    return preamble, records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    text = raw.decode("utf-8")
    preamble, records = parse(text)
    document = {
        "version": 1,
        "source": args.input.name,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "preamble": preamble,
        "records": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"indexed {len(records)} records; sha256={document['source_sha256']}")


if __name__ == "__main__":
    main()
