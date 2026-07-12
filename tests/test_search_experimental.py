import hashlib
import json
import unittest
from pathlib import Path

from search_engine_experimental.experiments.cone_dag import (
    ConeConfig,
    ConeDAG,
    ConeIndex,
)
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

    def test_cone_dag_is_deterministic_and_fixed_width(self):
        cone = ConeDAG(ConeConfig(width=64, seed=17))
        first = cone.encode("content position combination")
        second = cone.encode("content position combination")
        self.assertEqual(first, second)
        self.assertEqual(len(first.vector), 64 * 3 + 6)

    def test_cone_dag_keeps_local_edits_nearer_than_unrelated_text(self):
        cone = ConeDAG()
        source = "the riemann kernel is not a polya frequency function"
        typo = "the riemann kernel is not a polya frequnecy function"
        swap = "the riemann kernel is a not polya frequency function"
        unrelated = "jacobian maps polynomial automorphisms and monodromy"
        self.assertLess(cone.compare(source, typo)["distance"], cone.compare(source, unrelated)["distance"])
        self.assertLess(cone.compare(source, swap)["distance"], cone.compare(source, unrelated)["distance"])

    def test_cone_index_returns_exact_anchor(self):
        index = ConeIndex()
        original = "content position and combination define the sequence fingerprint"
        index.add("original", original)
        index.add("reversed", "fingerprint sequence the define combination and position content")
        index.add("other", "riemann xi kernel total positivity")
        result = index.search("content position combination define sequence fingerprint", limit=1)
        self.assertEqual(result[0][1], "original")
        self.assertEqual(result[0][2], original)

    def test_cone_rejects_unknown_position_mode(self):
        with self.assertRaises(ValueError):
            ConeDAG(ConeConfig(position_mode="opaque"))


if __name__ == "__main__":
    unittest.main()
