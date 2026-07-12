import hashlib
import json
import unittest
from pathlib import Path

from search_engine_experimental.experiments.sequence_fingerprint import compare


ROOT = Path(__file__).resolve().parent.parent


class ExperimentalSearchTest(unittest.TestCase):
    def test_local_research_manifest(self):
        base = ROOT / "search_engine_experimental" / "papers"
        manifest = json.loads((base / "MANIFEST.json").read_text())
        for name, expected in manifest.items():
            self.assertEqual(hashlib.sha256((base / name).read_bytes()).hexdigest(), expected)

    def test_sequence_sketch_separates_basic_relations(self):
        typo = compare("the riemann kernel is not pf5", "the reimann kernel is not pf5")["cosine"]
        reorder = compare("content position combination", "combination position content")["cosine"]
        unrelated = compare("riemann hypothesis kernel", "jacobian boundary monodromy")["cosine"]
        self.assertGreater(typo, reorder)
        self.assertGreater(typo, unrelated)


if __name__ == "__main__":
    unittest.main()
