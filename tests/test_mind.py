import json
import tempfile
import unittest
from pathlib import Path

from mindlib.search_backend import ExactTopicBackend
from mindlib.store import MindError, Store


class MindStoreTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "mind-data").mkdir(parents=True)
        self.store = Store(self.root)
        self.zeta, _ = self.store.add_topic("math", "zeta")

    def tearDown(self):
        self.tmp.cleanup()

    def test_orphan_then_anchor(self):
        base = self.store.establish("Base observation.", [self.zeta])
        self.assertEqual(self.store.factoids[base]["status"], "todo")
        child = self.store.establish("Derived observation.", [self.zeta], [base])
        self.assertEqual(self.store.factoids[child]["status"], "established")
        self.assertEqual(self.store.retrieval_roots({base}), [child])

    def test_cycle_rejected(self):
        first = self.store.establish("First.", [self.zeta])
        second = self.store.establish("Second.", [self.zeta], [first])
        with self.assertRaises(MindError):
            self.store.update_fact(first, "refer", [second])

    def test_citation_boundary_and_checksum(self):
        paper = self.root / "source.pdf"
        paper.write_bytes(b"paper")
        cite = self.store.add_citation("A", "B", [self.zeta], str(paper))
        fact = self.store.establish("Sourced.", [self.zeta])
        self.store.update_fact(fact, "refer", [cite], citation=True)
        self.assertEqual(self.store.factoids[fact]["status"], "established")
        self.assertEqual(self.store.validate(), [])

    def test_local_artifact_checksum(self):
        artifact = self.root / "source.txt"
        artifact.write_text("source", encoding="utf-8")
        cite = self.store.add_citation("A", "B", [self.zeta], artifacts=[artifact])
        self.assertEqual(self.store.validate(), [])
        artifact.write_text("changed", encoding="utf-8")
        self.assertIn("artifact checksum mismatch", " ".join(self.store.validate()))

    def test_exact_topic_backend_includes_descendants(self):
        child, _ = self.store.add_topic(self.zeta, "kernel")
        fact = self.store.establish("Kernel fact.", [child])
        matches, _ = ExactTopicBackend().resolve(self.store, "math/zeta")
        self.assertEqual(matches, {fact})

    def test_unused_leaf_prune_only(self):
        leaf, _ = self.store.add_topic(self.zeta, "unused")
        self.assertEqual(self.store.prune_topic(leaf), [leaf])
        self.assertIn(self.zeta, self.store.topics)


if __name__ == "__main__":
    unittest.main()
