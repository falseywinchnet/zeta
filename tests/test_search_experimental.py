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
from search_engine_experimental.experiments.drift_retrieval import (
    DriftAwareConeIndex,
    SubsequenceContainment,
    token_edit_distance,
)


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

    def test_order_containment_is_deletion_stable(self):
        sketch = SubsequenceContainment(sample_size=128, order_weight=1.0)
        source = "content position and combination preserve ordered sequence evidence"
        deleted = "content position combination preserve ordered sequence evidence"
        reversed_text = "evidence sequence ordered preserve combination and position content"
        self.assertEqual(sketch.compare(source, deleted), 1.0)
        self.assertLess(sketch.compare(source, reversed_text), 0.5)

    def test_local_containment_preserves_crop_and_detects_move(self):
        sketch = SubsequenceContainment(sample_size=128, order_weight=0.0)
        source = "alpha beta gamma delta epsilon zeta eta theta iota kappa"
        crop = "gamma delta epsilon zeta eta theta"
        moved = "alpha beta gamma epsilon delta zeta eta theta iota kappa"
        self.assertEqual(sketch.compare(source, crop), 1.0)
        self.assertLess(sketch.compare(moved, crop), 1.0)

    def test_token_edit_distance_exposes_erased_parent_ambiguity(self):
        query = "alpha beta delta"
        self.assertEqual(token_edit_distance(query, "alpha beta gamma delta"), 1)
        self.assertEqual(token_edit_distance(query, "alpha gamma beta delta"), 1)

    def test_drift_index_uses_containment_only_for_shorter_query(self):
        index = DriftAwareConeIndex()
        index.add("source", "alpha beta gamma delta epsilon zeta eta theta")
        index.add("other", "monodromy jacobian polynomial boundary infinity kernel")
        cropped = index.search("beta gamma delta epsilon zeta", limit=1)[0]
        self.assertEqual(cropped["id"], "source")
        self.assertTrue(cropped["directional"])
        equal_length = index.search("alpha beta gamma delta epsilon zeta eta iota", limit=1)[0]
        self.assertFalse(equal_length["directional"])
        self.assertIsNone(equal_length["containment_score"])


if __name__ == "__main__":
    unittest.main()
