import json
import tempfile
import unittest
from pathlib import Path

from mindlib.search_backend import ExactTopicBackend
from mindlib.search_index import SearchEngine, build_index, index_is_current
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

    def test_search_typo_and_stale_detection(self):
        kernel, _ = self.store.add_topic(self.zeta, "riemann-kernel")
        fact = self.store.establish("Schoenberg characterizes Polya frequency functions.", [kernel])
        build_index(self.store)
        results = SearchEngine(self.store).search("shoenberg polya", limit=3)
        self.assertEqual(results[0]["document"]["id"], fact)
        self.store.establish("A later fact.", [kernel])
        self.assertFalse(index_is_current(self.store))

    def test_search_indexes_work_and_graph_anchor(self):
        kernel, _ = self.store.add_topic(self.zeta, "kernel")
        base = self.store.establish("Interval arithmetic certifies a determinant.", [kernel])
        child = self.store.establish("The PF5 obstruction blocks total positivity.", [kernel], [base])
        work = self.root / "work" / "2026-01-01-test"
        work.mkdir(parents=True)
        (work / "ROUND.md").write_text("A raw spectral sibling experiment.", encoding="utf-8")
        build_index(self.store)
        engine = SearchEngine(self.store)
        self.assertEqual(engine.search("interval arithmetic, obstruction", 1)[0]["document"]["id"], child)
        self.assertEqual(engine.search("spectral sibling", 1, ["work"])[0]["document"]["kind"], "work")

    def test_progress_record_builds_static_index(self):
        self.store.establish("Indexed before commitment.", [self.zeta])
        pid = self.store.record_progress("index epoch")
        self.assertEqual(pid, "P000001")
        self.assertTrue(index_is_current(self.store))
        work = self.root / "work"
        work.mkdir()
        (work / "notes.md").write_text("changed after record", encoding="utf-8")
        self.assertFalse(index_is_current(self.store))

    def test_lossless_source_records_are_searchable(self):
        sources = self.root / "sources"
        sources.mkdir()
        document = {"records": [{"sequence": 1, "role": "response", "body": "A forgotten spectral armature phrase."}]}
        (sources / "sample.turns.json").write_text(json.dumps(document), encoding="utf-8")
        build_index(self.store)
        result = SearchEngine(self.store).search("forgotten spectral armature", 1, ["source"])[0]
        self.assertEqual(result["document"]["kind"], "source")


if __name__ == "__main__":
    unittest.main()
