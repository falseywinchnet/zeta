import json
import io
import math
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from mindlib.search_backend import ExactTopicBackend
from mindlib.identities import exact_identity, internal_id, public_id
from mindlib.cli import cmd_certificate, cmd_search
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
        self.assertEqual(self.store.factoids[child]["status"], "todo")
        cite = self.store.add_citation("A", "B", [self.zeta], artifacts=[self._file("source.txt", "source")])
        self.store.update_fact(base, "refer", [cite], citation=True)
        self.store.update_fact(child, "refer", [cite], citation=True)
        self.assertEqual(self.store.factoids[child]["status"], "established")
        self.assertEqual(self.store.retrieval_roots({base}), [child])

    def test_todo_child_does_not_hide_established_parent(self):
        cite = self.store.add_citation(
            "A", "B", [self.zeta], artifacts=[self._file("source.txt", "source")]
        )
        base = self.store.establish("Established base.", [self.zeta], [cite])
        child = self.store.establish("Uncertified continuation.", [self.zeta], [base])
        self.assertEqual(self.store.factoids[child]["status"], "todo")
        self.assertEqual(self.store.retrieval_roots({base}), [base])

    def _file(self, name, content):
        path = self.root / name
        path.write_text(content, encoding="utf-8")
        return path

    def test_cycle_rejected(self):
        first = self.store.establish("First.", [self.zeta])
        second = self.store.establish("Second.", [self.zeta], [first])
        with self.assertRaises(MindError):
            self.store.update_fact(first, "refer", [second])

    def test_factoid_content_can_be_modified_without_support_change(self):
        fact = self.store.establish("Original wording.", [self.zeta])
        self.store.modify_fact(fact, content="Corrected wording.")
        self.assertEqual(self.store.factoids[fact]["content"], "Corrected wording.")
        self.assertEqual(self.store.factoids[fact]["status"], "todo")

    def test_citation_boundary_and_checksum(self):
        paper = self.root / "source.pdf"
        paper.write_bytes(b"paper")
        cite = self.store.add_citation("A", "B", [self.zeta], str(paper))
        fact = self.store.establish("Sourced.", [self.zeta])
        self.store.update_fact(fact, "refer", [cite], citation=True)
        self.assertEqual(self.store.factoids[fact]["status"], "established")
        self.assertEqual(self.store.validate(), [])

    def test_citation_requires_local_evidence(self):
        with self.assertRaises(MindError):
            self.store.add_citation("A", "Unanchored.", [self.zeta])

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

    def test_progress_record_leaves_generated_index_lazy(self):
        self.store.establish("Indexed before commitment.", [self.zeta])
        pid = self.store.record_progress("index epoch")
        self.assertEqual(pid, "P000001")
        self.assertFalse(index_is_current(self.store))
        SearchEngine(self.store)
        self.assertTrue(index_is_current(self.store))
        work = self.root / "work"
        work.mkdir()
        (work / "notes.md").write_text("changed after record", encoding="utf-8")
        self.assertFalse(index_is_current(self.store))

    def test_replayable_certificate_and_output_hash(self):
        verifier = self._file("verify.py", "print('proof-ok')\n")
        kid = self.store.add_certificate(
            verifier,
            "Exact toy proof.",
            [self.zeta],
            requirements=[],
        )
        self.assertEqual(kid, "K000001")
        self.assertEqual(self.store.replay_certificates(kid), [kid])
        self.assertEqual(self.store.authenticate_certificates(kid), ([kid], []))
        manifest = self.store.certificate_manifest(kid)
        self.assertEqual(manifest["verifier"]["path"], "verify.py")
        self.assertEqual(
            self.store.certificates[kid]["attestation"]["manifest_sha256"],
            self.store.certificate_manifest_sha256(kid),
        )
        fact = self.store.establish("Certified theorem.", [self.zeta], [kid])
        self.assertEqual(self.store.factoids[fact]["status"], "established")
        verifier.write_text("print('changed')\n", encoding="utf-8")
        with self.assertRaises(MindError):
            self.store.replay_certificates(kid)

    def test_certificate_runner_must_invoke_registered_file(self):
        verifier = self._file("verify.py", "print('proof-ok')\n")
        with self.assertRaises(MindError):
            self.store.add_certificate(
                verifier, "Disconnected verifier.", [self.zeta], command="python3 -c pass"
            )

    def test_certificate_identity_is_reversible_and_searchable(self):
        verifier = self._file("verify.py", "print('proof-ok')\n")
        kid = self.store.add_certificate(verifier, "Spectral certificate boundary.", [self.zeta])
        self.assertEqual(public_id(kid), "CERT1")
        self.assertEqual(internal_id("cert1"), kid)
        self.assertEqual(exact_identity(self.store, "CERT1")["id"], kid)
        build_index(self.store)
        result = SearchEngine(self.store).search("spectral certificate", 1, ["certificate"])[0]
        self.assertEqual(result["document"]["id"], kid)

    def test_certificate_dependencies_replay_before_dependents(self):
        first_file = self._file("first.py", "print('first')\n")
        second_file = self._file("second.py", "print('second')\n")
        first = self.store.add_certificate(first_file, "First proof.", [self.zeta])
        second = self.store.add_certificate(
            second_file, "Dependent proof.", [self.zeta], dependencies=[first]
        )
        self.assertEqual(self.store.replay_certificates(second), [first, second])

    def test_archived_certificate_is_skipped_by_routine_replay(self):
        retired_file = self._file("retired.py", "print('retired')\n")
        active_file = self._file("active.py", "print('active')\n")
        retired = self.store.add_certificate(retired_file, "Retired proof.", [self.zeta])
        active = self.store.add_certificate(active_file, "Active proof.", [self.zeta])
        self.store.archive_certificate(retired)
        self.assertTrue(self.store.certificates[retired]["archived"])
        self.assertEqual(self.store.replay_certificates("ALL"), [active])
        self.assertEqual(self.store.authenticate_certificates("ALL"), ([active], []))
        self.assertEqual(self.store.replay_certificates(retired), [retired])

    def test_archive_guards_active_dependency_closure(self):
        first_file = self._file("first.py", "print('first')\n")
        second_file = self._file("second.py", "print('second')\n")
        first = self.store.add_certificate(first_file, "First proof.", [self.zeta])
        second = self.store.add_certificate(
            second_file, "Dependent proof.", [self.zeta], dependencies=[first]
        )
        with self.assertRaises(MindError):
            self.store.archive_certificate(first)
        self.store.archive_certificate(second)
        self.store.archive_certificate(first)
        with self.assertRaises(MindError):
            self.store.restore_certificate(second)
        third_file = self._file("third.py", "print('third')\n")
        with self.assertRaises(MindError):
            self.store.add_certificate(
                third_file, "Invalid active proof.", [self.zeta], dependencies=[first]
            )
        self.store.restore_certificate(first)
        self.store.restore_certificate(second)
        self.assertFalse(self.store.certificates[first].get("archived", False))
        self.assertFalse(self.store.certificates[second].get("archived", False))

    def test_changed_dependency_manifest_invalidates_dependent_attestation(self):
        first_file = self._file("first.py", "print('first')\n")
        second_file = self._file("second.py", "print('second')\n")
        first = self.store.add_certificate(first_file, "First proof.", [self.zeta])
        second = self.store.add_certificate(
            second_file, "Dependent proof.", [self.zeta], dependencies=[first]
        )
        first_file.write_text("print('first revised')\n", encoding="utf-8")
        self.store.change_certificate(first, filename=first_file)
        authenticated, replayed = self.store.authenticate_certificates(second)
        self.assertEqual(authenticated, [first])
        self.assertEqual(replayed, [second])

    def test_missing_attestation_is_replayed_once_then_authenticated(self):
        verifier = self._file("verify.py", "print('proof-ok')\n")
        kid = self.store.add_certificate(verifier, "Exact toy proof.", [self.zeta])
        del self.store.certificates[kid]["attestation"]
        authenticated, replayed = self.store.authenticate_certificates(kid)
        self.assertEqual(authenticated, [])
        self.assertEqual(replayed, [kid])
        self.assertEqual(self.store.authenticate_certificates(kid), ([kid], []))

    def test_certificate_cli_resolves_public_dependency(self):
        first_file = self._file("first.py", "print('first')\n")
        second_file = self._file("second.py", "print('second')\n")
        first = self.store.add_certificate(first_file, "First proof.", [self.zeta])
        with redirect_stdout(io.StringIO()):
            cmd_certificate(self.store, [
                "ADD", str(second_file), "--description", "Dependent proof.",
                "--topic", self.zeta, "--depends", public_id(first),
            ])
        self.assertEqual(self.store.certificates["K000002"]["dependencies"], [first])

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
        cite = self.store.add_citation(
            "Author", "Citation identity.", [self.zeta],
            artifacts=[self._file("citation.txt", "citation")],
        )
        self.assertEqual(public_id(fact), "R1")
        self.assertEqual(public_id(cite), "CITE1")
        self.assertEqual(internal_id("r1"), fact)
        self.assertEqual(internal_id("cite1"), cite)
        self.assertEqual(exact_identity(self.store, "R1")["id"], fact)
        self.assertEqual(exact_identity(self.store, "CITE1")["id"], cite)

    def test_search_merges_references_citations_and_topics(self):
        kernel, _ = self.store.add_topic(self.zeta, "spectral-kernel")
        fact = self.store.establish("Spectral determinant evidence.", [kernel])
        cite = self.store.add_citation(
            "Kernel Author", "Spectral source boundary.", [kernel],
            artifacts=[self._file("spectral.txt", "source")],
        )
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
        cite = self.store.add_citation(
            "Author", "Boundary body.", [self.zeta],
            artifacts=[self._file("boundary.txt", "source")],
        )
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
