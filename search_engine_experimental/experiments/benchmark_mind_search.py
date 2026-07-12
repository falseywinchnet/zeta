#!/usr/bin/env python3
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from mindlib.search_index import SearchEngine
from mindlib.store import Store


def main():
    cases = json.loads((Path(__file__).with_name("retrieval_benchmark.json")).read_text())
    engine = SearchEngine(Store(ROOT))
    passed = 0
    for case in cases:
        results = engine.search(case["query"], limit=case["at"])
        ids = [item["document"]["id"] for item in results]
        kinds = [item["document"]["kind"] for item in results]
        if "expected_ids" in case:
            ok = any(ident in ids for ident in case["expected_ids"])
        else:
            ok = case["expected_kind"] in kinds
        passed += ok
        print(f"{'PASS' if ok else 'FAIL'} {case['query']!r} -> {ids}")
    print(f"{passed}/{len(cases)} retrieval cases passed")
    return 0 if passed == len(cases) else 1


if __name__ == "__main__":
    raise SystemExit(main())
