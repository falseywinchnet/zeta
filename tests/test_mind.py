import json
import io
import math
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from mindlib.search_backend import ExactTopicBackend
from mindlib.identities import exact_identity, internal_id, public_id
from mindlib.cli import cmd_search
from mindlib.search_index import SearchEngine, build_index, dynamic_cutoff, index_is_current
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

    def test_public_reference_and_citation_identities_are_reversible(self):
        fact = self.store.establish("Reference identity.", [self.zeta])
        cite = self.store.add_citation("Author", "Citation identity.", [self.zeta])
        self.assertEqual(public_id(fact), "R1")
        self.assertEqual(public_id(cite), "CITE1")
        self.assertEqual(internal_id("r1"), fact)
        self.assertEqual(internal_id("cite1"), cite)
        self.assertEqual(exact_identity(self.store, "R1")["id"], fact)
        self.assertEqual(exact_identity(self.store, "CITE1")["id"], cite)

    def test_search_merges_references_citations_and_topics(self):
        kernel, _ = self.store.add_topic(self.zeta, "spectral-kernel")
        fact = self.store.establish("Spectral determinant evidence.", [kernel])
        cite = self.store.add_citation("Kernel Author", "Spectral source boundary.", [kernel])
        build_index(self.store)
        results = SearchEngine(self.store).search(
            "spectral kernel", limit=25, score_floor=0.0, secretary_count=1
        )
        kinds = {result["document"]["kind"] for result in results}
        identities = {result["document"]["id"] for result in results}
        self.assertIn(fact, identities)
        self.assertIn(cite, identities)
        self.assertIn("factoid", kinds)
        self.assertIn("citation", kinds)
        self.assertIn("topic", kinds)

    def test_dynamic_cutoff_uses_one_over_e_floor_after_eight_results(self):
        floor = math.exp(-1)
        ranked = [{"score": score} for score in (0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.38, floor, 0.367, 0.2)]
        selected = dynamic_cutoff(ranked, limit=25)
        self.assertEqual(len(selected), 8)
        self.assertEqual(selected[-1]["cutoff"]["mode"], "score-floor")
        self.assertEqual(selected[-1]["cutoff"]["qualifying_count"], 8)
        self.assertAlmostEqual(selected[-1]["cutoff"]["threshold"], floor)

    def test_dynamic_cutoff_uses_adjacent_one_over_e_fallback_below_eight(self):
        ranked = [{"score": score} for score in (0.9, 0.7, 0.5, 0.4, 0.38, 0.35, 0.34, 0.12, 0.1)]
        selected = dynamic_cutoff(ranked, limit=25)
        self.assertEqual(len(selected), 7)
        cutoff = selected[-1]["cutoff"]
        self.assertEqual(cutoff["mode"], "adjacent-fallback")
        self.assertEqual(cutoff["qualifying_count"], 5)
        self.assertLess(cutoff["ratio"], math.exp(-1))

    def test_dynamic_cutoff_fallback_respects_safety_limit(self):
        ranked = [{"score": score} for score in (0.9, 0.7, 0.5, 0.35, 0.3, 0.25, 0.2, 0.18, 0.16)]
        selected = dynamic_cutoff(ranked, limit=8)
        self.assertEqual(len(selected), 8)
        self.assertNotIn("cutoff", selected[-1])

    def test_dynamic_cutoff_fallback_drop_is_strict(self):
        floor = math.exp(-1)
        ranked = [{"score": 0.9}, {"score": 0.5}, {"score": 0.5 * floor}, {"score": 0.05}]
        selected = dynamic_cutoff(ranked, limit=25)
        self.assertEqual(len(selected), 3)

    def test_search_exact_public_id_returns_full_object(self):
        cite = self.store.add_citation("Author", "Boundary body.", [self.zeta])
        fact = self.store.establish("Anchored reference.", [self.zeta])
        self.store.update_fact(fact, "refer", [cite], citation=True)
        output = io.StringIO()
        with redirect_stdout(output):
            cmd_search(self.store, ["R1"])
        self.assertIn("TRACEMAP 1", output.getvalue())
        self.assertIn("R1: Anchored reference.", output.getvalue())
        output = io.StringIO()
        with redirect_stdout(output):
            cmd_search(self.store, ["CITE1"])
        self.assertIn("CITATION: CITE1", output.getvalue())
        self.assertIn("SUPPORTS: R1", output.getvalue())


if __name__ == "__main__":
    unittest.main()
