from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
COLLECTIONS = ("factoids", "citations", "taxonomy", "progress")
PATTERNS = {
    "factoids": re.compile(r"^F\d{6}$"),
    "citations": re.compile(r"^C\d{6}$"),
    "taxonomy": re.compile(r"^T\d{6}$"),
    "progress": re.compile(r"^P\d{6}$"),
}


def now():
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def atomic_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    fd, tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


class MindError(RuntimeError):
    pass


class Store:
    def __init__(self, root=ROOT):
        self.root = Path(root)
        self.data_dir = self.root / "mind-data"
        self.paths = {name: self.data_dir / f"{name}.json" for name in COLLECTIONS}
        self._ensure()
        self.reload()

    def _ensure(self):
        self.data_dir.mkdir(parents=True, exist_ok=True)
        defaults = {
            "factoids": {"version": 1, "next_id": 1, "items": {}},
            "citations": {"version": 1, "next_id": 1, "items": {}},
            "taxonomy": {
                "version": 1,
                "next_id": 2,
                "items": {"T000001": {"label": "math", "parent": None, "created_at": now()}},
            },
            "progress": {"version": 1, "next_id": 1, "items": {}},
        }
        for name, path in self.paths.items():
            if not path.exists():
                atomic_json(path, defaults[name])

    def reload(self):
        self.docs = {}
        for name, path in self.paths.items():
            try:
                self.docs[name] = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                raise MindError(f"cannot load {path}: {exc}") from exc
        self.factoids = self.docs["factoids"]["items"]
        self.citations = self.docs["citations"]["items"]
        self.topics = self.docs["taxonomy"]["items"]
        self.progress = self.docs["progress"]["items"]

    def save(self, name):
        atomic_json(self.paths[name], self.docs[name])

    def allocate(self, collection, prefix):
        doc = self.docs[collection]
        ident = f"{prefix}{doc['next_id']:06d}"
        doc["next_id"] += 1
        return ident

    def resolve_topic(self, value):
        if value is None:
            return None
        value = value.strip()
        upper = value.upper()
        if upper in self.topics:
            return upper
        exact = [tid for tid, item in self.topics.items() if item["label"].casefold() == value.casefold()]
        if len(exact) == 1:
            return exact[0]
        paths = [tid for tid in self.topics if self.topic_path(tid).casefold() == value.casefold()]
        if len(paths) == 1:
            return paths[0]
        if len(exact) > 1:
            raise MindError(f"ambiguous topic {value!r}; use an ID or full path")
        return None

    def topic_path(self, topic_id):
        if topic_id not in self.topics:
            raise MindError(f"unknown topic: {topic_id}")
        labels, seen, cur = [], set(), topic_id
        while cur is not None:
            if cur in seen:
                raise MindError(f"taxonomy cycle at {cur}")
            seen.add(cur)
            labels.append(self.topics[cur]["label"])
            cur = self.topics[cur]["parent"]
        return "/".join(reversed(labels))

    def topic_descendants(self, topic_id):
        found, frontier = set(), [topic_id]
        while frontier:
            parent = frontier.pop()
            for child, item in self.topics.items():
                if item["parent"] == parent and child not in found:
                    found.add(child)
                    frontier.append(child)
        return found

    def _topic_ids(self, topics):
        result = []
        for topic in topics or []:
            tid = self.resolve_topic(topic)
            if tid is None:
                raise MindError(f"unknown topic: {topic}")
            if tid not in result:
                result.append(tid)
        if not result:
            raise MindError("at least one valid topic is required")
        return result

    def add_topic(self, parent, label):
        parent_id = self.resolve_topic(parent)
        if parent_id is None:
            raise MindError(f"unknown parent topic: {parent}")
        label = label.strip()
        if not label or "/" in label:
            raise MindError("topic label must be nonempty and cannot contain '/'")
        for tid, item in self.topics.items():
            if item["parent"] == parent_id and item["label"].casefold() == label.casefold():
                return tid, False
        tid = self.allocate("taxonomy", "T")
        self.topics[tid] = {"label": label, "parent": parent_id, "created_at": now()}
        self.save("taxonomy")
        return tid, True

    def prune_topic(self, value=None):
        if value is None:
            candidates = [tid for tid in self.topics if tid != "T000001"]
        else:
            tid = self.resolve_topic(value)
            if tid is None:
                raise MindError(f"unknown topic: {value}")
            candidates = [tid]
        removed = []
        for tid in sorted(candidates, reverse=True):
            child = any(item["parent"] == tid for item in self.topics.values())
            used = any(tid in fact["relates_to"] for fact in self.factoids.values()) or any(
                tid in cite["topics"] for cite in self.citations.values()
            )
            if not child and not used and tid in self.topics:
                del self.topics[tid]
                removed.append(tid)
        if removed:
            self.save("taxonomy")
        return removed

    def add_citation(self, author, body, topics, paper=None, source_url=None):
        paper_record = self._copy_paper(paper) if paper else None
        cid = self.allocate("citations", "C")
        self.citations[cid] = {
            "author": author.strip(), "body": body.strip(), "topics": self._topic_ids(topics),
            "paper": paper_record, "source_url": source_url, "created_at": now(), "updated_at": now(),
        }
        self.save("citations")
        return cid

    def _copy_paper(self, paper):
        source = Path(paper).expanduser().resolve()
        if not source.is_file():
            raise MindError(f"paper does not exist: {source}")
        target = self.root / "papers" / source.name
        target.parent.mkdir(parents=True, exist_ok=True)
        if source != target:
            shutil.copy2(source, target)
        return {"path": str(target.relative_to(self.root)), "sha256": hashlib.sha256(target.read_bytes()).hexdigest()}

    def remove_citation(self, cid):
        cid = cid.upper()
        if cid not in self.citations:
            raise MindError(f"unknown citation: {cid}")
        users = [fid for fid, fact in self.factoids.items() if {"type": "citation", "id": cid} in fact["because"]]
        if users:
            raise MindError(f"citation {cid} supports: {', '.join(users)}")
        del self.citations[cid]
        self.save("citations")

    def change_citation(self, cid, author=None, body=None, topics=None, paper=None, source_url=None):
        cid = cid.upper()
        if cid not in self.citations:
            raise MindError(f"unknown citation: {cid}")
        item = self.citations[cid]
        for field, value in (("author", author), ("body", body), ("source_url", source_url)):
            if value is not None:
                item[field] = value.strip()
        if topics is not None:
            item["topics"] = self._topic_ids(topics)
        if paper is not None:
            item["paper"] = self._copy_paper(paper)
        item["updated_at"] = now()
        self.save("citations")

    def establish(self, content, topics, because=None):
        text = content.strip()
        if not text:
            raise MindError("factoid content cannot be empty")
        duplicates = [fid for fid, fact in self.factoids.items() if fact["content"] == text]
        if duplicates:
            raise MindError(f"duplicate content already stored as {duplicates[0]}")
        refs = []
        for fid in because or []:
            fid = fid.upper()
            if fid not in self.factoids:
                raise MindError(f"unknown factoid: {fid}")
            ref = {"type": "factoid", "id": fid}
            if ref not in refs:
                refs.append(ref)
        fid = self.allocate("factoids", "F")
        timestamp = now()
        self.factoids[fid] = {
            "content": text, "because": refs, "relates_to": self._topic_ids(topics),
            "status": "established" if refs else "todo", "created_at": timestamp, "updated_at": timestamp,
        }
        self._assert_acyclic()
        self.save("factoids")
        return fid

    def update_fact(self, fid, action, refs, citation=False, content=None, topics=None):
        fid = fid.upper()
        if fid not in self.factoids:
            raise MindError(f"unknown factoid: {fid}")
        fact = self.factoids[fid]
        kind = "citation" if citation else "factoid"
        valid = self.citations if citation else self.factoids
        normalized = []
        for ident in refs:
            ident = ident.upper()
            if ident not in valid:
                raise MindError(f"unknown {kind}: {ident}")
            if kind == "factoid" and ident == fid:
                raise MindError("a factoid cannot support itself")
            normalized.append({"type": kind, "id": ident})
        if action == "refer":
            for ref in normalized:
                if ref not in fact["because"]:
                    fact["because"].append(ref)
        elif action == "prune":
            missing = [ref["id"] for ref in normalized if ref not in fact["because"]]
            if missing:
                raise MindError(f"not direct supports of {fid}: {', '.join(missing)}")
            fact["because"] = [ref for ref in fact["because"] if ref not in normalized]
        else:
            raise MindError(f"unknown update action: {action}")
        if content is not None:
            if not content.strip():
                raise MindError("replacement content cannot be empty")
            fact["content"] = content.strip()
        if topics is not None:
            fact["relates_to"] = self._topic_ids(topics)
        fact["status"] = "established" if fact["because"] else "todo"
        fact["updated_at"] = now()
        self._assert_acyclic()
        self.save("factoids")

    def _assert_acyclic(self):
        visiting, visited = set(), set()

        def visit(fid):
            if fid in visiting:
                raise MindError(f"causal cycle involving {fid}")
            if fid in visited:
                return
            visiting.add(fid)
            for ref in self.factoids[fid]["because"]:
                if ref["type"] == "factoid":
                    visit(ref["id"])
            visiting.remove(fid)
            visited.add(fid)

        for fid in self.factoids:
            visit(fid)

    def reverse_refs(self):
        reverse = {fid: set() for fid in self.factoids}
        for parent, fact in self.factoids.items():
            for ref in fact["because"]:
                if ref["type"] == "factoid":
                    reverse[ref["id"]].add(parent)
        return reverse

    def retrieval_roots(self, matches):
        reverse = self.reverse_refs()
        reachable, frontier = set(matches), list(matches)
        while frontier:
            fid = frontier.pop()
            for parent in reverse.get(fid, ()):
                if parent not in reachable:
                    reachable.add(parent)
                    frontier.append(parent)
        standalone = [fid for fid in reachable if not reverse[fid] and self.factoids[fid]["status"] == "established"]
        return sorted(standalone, key=lambda fid: (self.factoids[fid]["updated_at"], fid), reverse=True)

    def trace_closure(self, root):
        ordered, seen = [], set()

        def walk(fid, depth):
            if fid in seen:
                return
            seen.add(fid)
            ordered.append((fid, depth))
            for ref in self.factoids[fid]["because"]:
                if ref["type"] == "factoid":
                    walk(ref["id"], depth + 1)

        walk(root, 0)
        return ordered

    def progress_commit_map(self):
        mapping = {}
        result = subprocess.run(["git", "log", "--format=%H%x09%s"], cwd=self.root, text=True, capture_output=True)
        for line in result.stdout.splitlines():
            commit, _, subject = line.partition("\t")
            match = re.match(r"mind\((P\d{6})\):", subject)
            if match and match.group(1) not in mapping:
                mapping[match.group(1)] = commit
        return mapping

    def pending_progress(self):
        committed = self.progress_commit_map()
        pending = [pid for pid in self.progress if pid not in committed]
        return sorted(pending)[-1] if pending else None

    def record_progress(self, blurb):
        blurb = blurb.strip()
        if not blurb:
            raise MindError("progress blurb cannot be empty")
        pending = self.pending_progress()
        if pending:
            raise MindError(f"{pending} is not committed; change or commit it first")
        pid = self.allocate("progress", "P")
        self.progress[pid] = {"blurb": blurb, "created_at": now()}
        self.save("progress")
        return pid

    def change_progress(self, pid, blurb):
        pid = pid.upper()
        if pid not in self.progress:
            raise MindError(f"unknown progress record: {pid}")
        if pid in self.progress_commit_map():
            raise MindError("committed progress is immutable; record a corrective epoch")
        if pid != self.pending_progress():
            raise MindError("only the current uncommitted progress record can change")
        self.progress[pid]["blurb"] = blurb.strip()
        self.progress[pid]["updated_at"] = now()
        self.save("progress")

    def validate(self):
        errors = []
        for name, doc in self.docs.items():
            if doc.get("version") != 1 or not isinstance(doc.get("items"), dict):
                errors.append(f"{name}: malformed document header")
            for ident in doc.get("items", {}):
                if not PATTERNS[name].match(ident):
                    errors.append(f"{name}: malformed ID {ident}")
        if "T000001" not in self.topics or self.topics["T000001"].get("parent") is not None:
            errors.append("taxonomy: T000001 math root missing or parented")
        try:
            for tid in self.topics:
                self.topic_path(tid)
            self._assert_acyclic()
        except MindError as exc:
            errors.append(str(exc))
        for fid, fact in self.factoids.items():
            required = {"content", "because", "relates_to", "status", "created_at", "updated_at"}
            if not required.issubset(fact):
                errors.append(f"{fid}: missing fields {sorted(required - set(fact))}")
                continue
            for tid in fact["relates_to"]:
                if tid not in self.topics:
                    errors.append(f"{fid}: unknown topic {tid}")
            for ref in fact["because"]:
                valid = self.factoids if ref.get("type") == "factoid" else self.citations if ref.get("type") == "citation" else {}
                if ref.get("id") not in valid:
                    errors.append(f"{fid}: invalid support {ref}")
            expected = "established" if fact["because"] else "todo"
            if fact["status"] != expected:
                errors.append(f"{fid}: status should be {expected}")
        for cid, cite in self.citations.items():
            for tid in cite.get("topics", []):
                if tid not in self.topics:
                    errors.append(f"{cid}: unknown topic {tid}")
            paper = cite.get("paper")
            if paper:
                path = self.root / paper["path"]
                if not path.is_file():
                    errors.append(f"{cid}: missing local paper {paper['path']}")
                elif hashlib.sha256(path.read_bytes()).hexdigest() != paper["sha256"]:
                    errors.append(f"{cid}: paper checksum mismatch")
        return errors

    def run_commit(self):
        pid = self.pending_progress()
        if not pid:
            raise MindError("PROGRESS RECORD is required after the previous epoch")
        errors = self.validate()
        if errors:
            raise MindError("validation failed:\n  " + "\n  ".join(errors))
        py = os.environ.get("PYTHON", "python3")
        if subprocess.run([py, "-m", "compileall", "-q", "mindlib", "tests"], cwd=self.root).returncode:
            raise MindError("Python compilation failed")
        if subprocess.run([py, "-m", "unittest", "discover", "-s", "tests", "-q"], cwd=self.root).returncode:
            raise MindError("tests failed")
        status = subprocess.run(["git", "status", "--porcelain"], cwd=self.root, text=True, capture_output=True)
        if not status.stdout.strip():
            raise MindError("no changes to commit")
        subprocess.run(["git", "add", "-A"], cwd=self.root, check=True)
        subject = f"mind({pid}): {self.progress[pid]['blurb']}"
        if subprocess.run(["git", "commit", "-m", subject], cwd=self.root).returncode:
            raise MindError("git commit failed; index remains staged")
        branch = subprocess.run(["git", "branch", "--show-current"], cwd=self.root, text=True, capture_output=True, check=True).stdout.strip()
        if subprocess.run(["git", "push", "origin", branch], cwd=self.root).returncode:
            raise MindError(f"commit created on {branch}, but push failed")
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.root, text=True, capture_output=True, check=True).stdout.strip()
        return pid, commit, branch
