from __future__ import annotations

import hashlib
import importlib.metadata
import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
COLLECTIONS = ("factoids", "citations", "certificates", "taxonomy", "progress")
PATTERNS = {
    "factoids": re.compile(r"^F\d{6}$"),
    "citations": re.compile(r"^C\d{6}$"),
    "certificates": re.compile(r"^K\d{6}$"),
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
            "certificates": {"version": 1, "next_id": 1, "items": {}},
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
        self.certificates = self.docs["certificates"]["items"]
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
            ) or any(
                tid in certificate["topics"] for certificate in self.certificates.values()
            )
            if not child and not used and tid in self.topics:
                del self.topics[tid]
                removed.append(tid)
        if removed:
            self.save("taxonomy")
        return removed

    def add_citation(self, author, body, topics, paper=None, source_url=None, artifacts=None):
        if not paper and not artifacts:
            raise MindError("citation requires a local paper or source artifact")
        paper_record = self._copy_paper(paper) if paper else None
        cid = self.allocate("citations", "C")
        self.citations[cid] = {
            "author": author.strip(), "body": body.strip(), "topics": self._topic_ids(topics),
            "paper": paper_record, "artifacts": self._artifact_records(artifacts or []),
            "source_url": source_url, "created_at": now(), "updated_at": now(),
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

    def _artifact_records(self, artifacts):
        records = []
        for artifact in artifacts:
            path = Path(artifact).expanduser()
            path = path if path.is_absolute() else self.root / path
            path = path.resolve()
            try:
                relative = path.relative_to(self.root.resolve())
            except ValueError as exc:
                raise MindError(f"artifact must already be inside the repository: {path}") from exc
            if not path.is_file():
                raise MindError(f"artifact does not exist: {path}")
            records.append({"path": str(relative), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        return records

    def _file_record(self, filename):
        records = self._artifact_records([filename])
        return records[0]

    def _certificate_argv(self, filename, command):
        if command:
            try:
                argv = shlex.split(command)
            except ValueError as exc:
                raise MindError(f"invalid verifier command: {exc}") from exc
            if not argv:
                raise MindError("verifier command cannot be empty")
            return argv
        path = Path(filename)
        if path.suffix.casefold() == ".py":
            return ["{python}", str(path)]
        return [str(path)]

    def _normalize_certificate_dependencies(self, dependencies):
        result = []
        for dependency in dependencies or []:
            dependency = dependency.upper()
            if dependency not in self.certificates:
                raise MindError(f"unknown certificate: {dependency}")
            if dependency not in result:
                result.append(dependency)
        return result

    def _check_requirements(self, requirements):
        for requirement in requirements or []:
            name, separator, expected = requirement.partition("==")
            if not separator or not name.strip() or not expected.strip():
                raise MindError(f"requirement must use package==version: {requirement}")
            try:
                observed = importlib.metadata.version(name.strip())
            except importlib.metadata.PackageNotFoundError as exc:
                raise MindError(f"certificate requirement missing: {name.strip()}") from exc
            if observed != expected.strip():
                raise MindError(
                    f"certificate requirement mismatch: {name.strip()}=={expected.strip()} required, {observed} installed"
                )

    def _replay_certificate_item(self, item, compare_output=True):
        files = [item["file"], *item.get("artifacts", [])]
        for record in files:
            path = self.root / record["path"]
            if not path.is_file():
                raise MindError(f"certificate file missing: {record['path']}")
            observed = hashlib.sha256(path.read_bytes()).hexdigest()
            if observed != record["sha256"]:
                raise MindError(f"certificate checksum mismatch: {record['path']}")
        self._check_requirements(item.get("requirements", []))
        environment = item.get("environment")
        if environment:
            observed = os.environ.get("MIND_ENVIRONMENT_DIGEST")
            if observed != environment:
                raise MindError(
                    "certificate environment mismatch: set MIND_ENVIRONMENT_DIGEST "
                    f"to {environment!r} (observed {observed!r})"
                )
        argv = [os.environ.get("PYTHON", "python3") if arg == "{python}" else arg for arg in item["runner"]["argv"]]
        try:
            result = subprocess.run(
                argv,
                cwd=self.root,
                text=False,
                capture_output=True,
                timeout=item["runner"]["timeout_seconds"],
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise MindError(f"certificate runner failed to execute {' '.join(argv)}: {exc}") from exc
        expected_exit = item["runner"].get("expected_exit_code", 0)
        if result.returncode != expected_exit:
            stderr = result.stderr.decode("utf-8", errors="replace")[-1000:]
            raise MindError(
                f"certificate runner exited {result.returncode}, expected {expected_exit}: {' '.join(argv)}\n{stderr}"
            )
        hashes = {
            "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
            "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
        }
        if compare_output:
            for field, observed in hashes.items():
                expected = item["runner"].get(field)
                if expected != observed:
                    raise MindError(
                        f"certificate {field.removesuffix('_sha256')} mismatch: expected {expected}, observed {observed}"
                    )
        return hashes

    def add_certificate(
        self, filename, description, topics, command=None, artifacts=None,
        requirements=None, precision=None, environment=None, dependencies=None, timeout_seconds=300,
    ):
        description = description.strip()
        if not description:
            raise MindError("certificate description cannot be empty")
        file_record = self._file_record(filename)
        argv = self._certificate_argv(file_record["path"], command)
        if file_record["path"] not in argv:
            raise MindError("verifier command must include the certificate FILE as an argument")
        item = {
            "description": description,
            "topics": self._topic_ids(topics),
            "file": file_record,
            "artifacts": self._artifact_records(artifacts or []),
            "dependencies": self._normalize_certificate_dependencies(dependencies),
            "requirements": list(requirements or []),
            "precision": precision,
            "environment": environment,
            "runner": {
                "argv": argv,
                "timeout_seconds": int(timeout_seconds),
                "expected_exit_code": 0,
            },
            "created_at": now(),
            "updated_at": now(),
        }
        if item["runner"]["timeout_seconds"] <= 0:
            raise MindError("certificate timeout must be positive")
        self._check_requirements(item["requirements"])
        item["runner"].update(self._replay_certificate_item(item, compare_output=False))
        kid = self.allocate("certificates", "K")
        self.certificates[kid] = item
        self._assert_certificate_acyclic()
        self.save("certificates")
        return kid

    def change_certificate(
        self, kid, filename=None, description=None, topics=None, command=None, artifacts=None,
        requirements=None, precision=None, environment=None, dependencies=None, timeout_seconds=None,
    ):
        kid = kid.upper()
        if kid not in self.certificates:
            raise MindError(f"unknown certificate: {kid}")
        item = self.certificates[kid]
        if filename is not None:
            item["file"] = self._file_record(filename)
        if description is not None:
            if not description.strip():
                raise MindError("certificate description cannot be empty")
            item["description"] = description.strip()
        if topics is not None:
            item["topics"] = self._topic_ids(topics)
        if artifacts is not None:
            item["artifacts"] = self._artifact_records(artifacts)
        if requirements is not None:
            item["requirements"] = list(requirements)
        if precision is not None:
            item["precision"] = precision
        if environment is not None:
            item["environment"] = environment
        if dependencies is not None:
            item["dependencies"] = self._normalize_certificate_dependencies(dependencies)
        if timeout_seconds is not None:
            if timeout_seconds <= 0:
                raise MindError("certificate timeout must be positive")
            item["runner"]["timeout_seconds"] = timeout_seconds
        if command is not None:
            item["runner"]["argv"] = self._certificate_argv(item["file"]["path"], command)
        if item["file"]["path"] not in item["runner"]["argv"]:
            raise MindError("verifier command must include the certificate FILE as an argument")
        self._assert_certificate_acyclic()
        item["runner"].update(self._replay_certificate_item(item, compare_output=False))
        item["updated_at"] = now()
        self.save("certificates")

    def remove_certificate(self, kid):
        kid = kid.upper()
        if kid not in self.certificates:
            raise MindError(f"unknown certificate: {kid}")
        users = [fid for fid, fact in self.factoids.items() if {"type": "certificate", "id": kid} in fact["because"]]
        dependencies = [
            other for other, item in self.certificates.items() if kid in item.get("dependencies", [])
        ]
        if users or dependencies:
            details = users + dependencies
            raise MindError(f"certificate {kid} supports: {', '.join(details)}")
        del self.certificates[kid]
        self.save("certificates")

    def _assert_certificate_acyclic(self):
        visiting, visited = set(), set()

        def visit(kid):
            if kid in visiting:
                raise MindError(f"certificate dependency cycle involving {kid}")
            if kid in visited:
                return
            visiting.add(kid)
            for dependency in self.certificates[kid].get("dependencies", []):
                if dependency not in self.certificates:
                    raise MindError(f"{kid}: unknown certificate dependency {dependency}")
                visit(dependency)
            visiting.remove(kid)
            visited.add(kid)

        for kid in self.certificates:
            visit(kid)

    def replay_certificates(self, target=None):
        target = target.upper() if target else "ALL"
        if target != "ALL" and target not in self.certificates:
            raise MindError(f"unknown certificate: {target}")
        roots = sorted(self.certificates) if target == "ALL" else [target]
        selected = set()

        def visit(kid):
            if kid in selected:
                return
            for dependency in self.certificates[kid].get("dependencies", []):
                visit(dependency)
            selected.add(kid)

        for kid in roots:
            visit(kid)
        ordered, completed = [], set()
        workers = max(1, int(os.environ.get("MIND_CERTIFICATE_JOBS", "4")))
        while completed != selected:
            ready = sorted(
                kid for kid in selected - completed
                if set(self.certificates[kid].get("dependencies", [])) <= completed
            )
            if not ready:
                raise MindError("certificate dependency graph has no replayable frontier")
            with ThreadPoolExecutor(max_workers=min(workers, len(ready))) as executor:
                futures = {
                    kid: executor.submit(
                        self._replay_certificate_item,
                        self.certificates[kid],
                        True,
                    )
                    for kid in ready
                }
                for kid in ready:
                    futures[kid].result()
            completed.update(ready)
            ordered.extend(ready)
        return ordered

    def remove_citation(self, cid):
        cid = cid.upper()
        if cid not in self.citations:
            raise MindError(f"unknown citation: {cid}")
        users = [fid for fid, fact in self.factoids.items() if {"type": "citation", "id": cid} in fact["because"]]
        if users:
            raise MindError(f"citation {cid} supports: {', '.join(users)}")
        del self.citations[cid]
        self.save("citations")

    def change_citation(self, cid, author=None, body=None, topics=None, paper=None, source_url=None, artifacts=None):
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
        if artifacts is not None:
            item["artifacts"] = self._artifact_records(artifacts)
        item["updated_at"] = now()
        self.save("citations")

    def _normalize_supports(self, supports):
        normalized = []
        for support in supports or []:
            if isinstance(support, dict):
                kind, ident = support.get("type"), str(support.get("id", "")).upper()
            else:
                ident = str(support).upper()
                if ident in self.factoids:
                    kind = "factoid"
                elif ident in self.citations:
                    kind = "citation"
                elif ident in self.certificates:
                    kind = "certificate"
                else:
                    raise MindError(f"unknown support: {support}")
            valid = {
                "factoid": self.factoids,
                "citation": self.citations,
                "certificate": self.certificates,
            }.get(kind)
            if valid is None or ident not in valid:
                raise MindError(f"unknown {kind or 'support'}: {ident}")
            ref = {"type": kind, "id": ident}
            if ref not in normalized:
                normalized.append(ref)
        return normalized

    def _derived_statuses(self):
        statuses = {}

        def status(fid):
            if fid in statuses:
                return statuses[fid]
            fact = self.factoids[fid]
            boundary = any(ref["type"] in {"citation", "certificate"} for ref in fact["because"])
            prerequisites = [ref["id"] for ref in fact["because"] if ref["type"] == "factoid"]
            value = "established" if boundary and all(status(parent) == "established" for parent in prerequisites) else "todo"
            statuses[fid] = value
            return value

        self._assert_acyclic()
        for fid in self.factoids:
            status(fid)
        return statuses

    def refresh_statuses(self, save=False):
        statuses = self._derived_statuses()
        changed = []
        for fid, expected in statuses.items():
            if self.factoids[fid].get("status") != expected:
                self.factoids[fid]["status"] = expected
                changed.append(fid)
        if changed and save:
            self.save("factoids")
        return changed

    def establish(self, content, topics, because=None):
        text = content.strip()
        if not text:
            raise MindError("factoid content cannot be empty")
        duplicates = [fid for fid, fact in self.factoids.items() if fact["content"] == text]
        if duplicates:
            raise MindError(f"duplicate content already stored as {duplicates[0]}")
        refs = self._normalize_supports(because)
        fid = self.allocate("factoids", "F")
        timestamp = now()
        self.factoids[fid] = {
            "content": text, "because": refs, "relates_to": self._topic_ids(topics),
            "status": "todo", "created_at": timestamp, "updated_at": timestamp,
        }
        self._assert_acyclic()
        self.refresh_statuses()
        self.save("factoids")
        return fid

    def update_fact(
        self, fid, action, refs, support_type="factoid", content=None, topics=None, citation=False,
    ):
        fid = fid.upper()
        if fid not in self.factoids:
            raise MindError(f"unknown factoid: {fid}")
        fact = self.factoids[fid]
        kind = "citation" if citation else support_type
        valid = {
            "factoid": self.factoids,
            "citation": self.citations,
            "certificate": self.certificates,
        }.get(kind)
        if valid is None:
            raise MindError(f"unknown support type: {kind}")
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
        fact["updated_at"] = now()
        self._assert_acyclic()
        self.refresh_statuses()
        self.save("factoids")

    def modify_fact(self, fid, content=None, topics=None):
        fid = fid.upper()
        if fid not in self.factoids:
            raise MindError(f"unknown factoid: {fid}")
        if content is None and topics is None:
            raise MindError("MODIFY requires CONTENT or RELATES")
        fact = self.factoids[fid]
        if content is not None:
            if not content.strip():
                raise MindError("replacement content cannot be empty")
            duplicates = [
                other for other, item in self.factoids.items()
                if other != fid and item["content"] == content.strip()
            ]
            if duplicates:
                raise MindError(f"duplicate content already stored as {duplicates[0]}")
            fact["content"] = content.strip()
        if topics is not None:
            fact["relates_to"] = self._topic_ids(topics)
        fact["updated_at"] = now()
        self.refresh_statuses()
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
        standalone = [
            fid for fid in reachable
            if self.factoids[fid]["status"] == "established"
            and not any(self.factoids[parent]["status"] == "established" for parent in reverse[fid])
        ]
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
                valid = {
                    "factoid": self.factoids,
                    "citation": self.citations,
                    "certificate": self.certificates,
                }.get(ref.get("type"), {})
                if ref.get("id") not in valid:
                    errors.append(f"{fid}: invalid support {ref}")
            expected = self._derived_statuses().get(fid, "todo")
            if fact["status"] != expected:
                errors.append(f"{fid}: status should be {expected}")
        for cid, cite in self.citations.items():
            if not cite.get("paper") and not cite.get("artifacts"):
                errors.append(f"{cid}: citation has no local evidence")
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
            for artifact in cite.get("artifacts", []):
                path = self.root / artifact["path"]
                if not path.is_file():
                    errors.append(f"{cid}: missing local artifact {artifact['path']}")
                elif hashlib.sha256(path.read_bytes()).hexdigest() != artifact["sha256"]:
                    errors.append(f"{cid}: artifact checksum mismatch for {artifact['path']}")
        try:
            self._assert_certificate_acyclic()
        except MindError as exc:
            errors.append(str(exc))
        for kid, certificate in self.certificates.items():
            required = {"description", "topics", "file", "runner", "created_at", "updated_at"}
            if not required.issubset(certificate):
                errors.append(f"{kid}: missing fields {sorted(required - set(certificate))}")
                continue
            runner_required = {
                "argv", "timeout_seconds", "expected_exit_code", "stdout_sha256", "stderr_sha256"
            }
            missing_runner = runner_required - set(certificate["runner"])
            if missing_runner:
                errors.append(f"{kid}: runner missing fields {sorted(missing_runner)}")
            elif certificate["file"]["path"] not in certificate["runner"]["argv"]:
                errors.append(f"{kid}: runner does not invoke certificate file")
            for tid in certificate["topics"]:
                if tid not in self.topics:
                    errors.append(f"{kid}: unknown topic {tid}")
            for record in [certificate["file"], *certificate.get("artifacts", [])]:
                path = self.root / record["path"]
                if not path.is_file():
                    errors.append(f"{kid}: missing certificate file {record['path']}")
                elif hashlib.sha256(path.read_bytes()).hexdigest() != record["sha256"]:
                    errors.append(f"{kid}: certificate checksum mismatch for {record['path']}")
        return errors

    def run_commit(self):
        pid = self.pending_progress()
        if not pid:
            raise MindError("PROGRESS RECORD is required after the previous epoch")
        errors = self.validate()
        if errors:
            raise MindError("validation failed:\n  " + "\n  ".join(errors))
        replayed = self.replay_certificates("ALL")
        from .search_index import build_index, index_is_current

        build_index(self)
        if not index_is_current(self):
            raise MindError("generated search index is stale")
        py = os.environ.get("PYTHON", "python3")
        if subprocess.run([py, "-m", "compileall", "-q", "mindlib", "tests", "search_engine_experimental"], cwd=self.root).returncode:
            raise MindError("Python compilation failed")
        if subprocess.run([py, "-m", "unittest", "discover", "-s", "tests", "-q"], cwd=self.root).returncode:
            raise MindError("tests failed")
        status = subprocess.run(["git", "status", "--porcelain"], cwd=self.root, text=True, capture_output=True)
        if not status.stdout.strip():
            raise MindError("no changes to commit")
        subprocess.run(
            ["git", "rm", "--cached", "--ignore-unmatch", "mind-data/search-index.json"],
            cwd=self.root,
            check=True,
            stdout=subprocess.DEVNULL,
        )
        subprocess.run(["git", "add", "-A"], cwd=self.root, check=True)
        subject = f"mind({pid}): {self.progress[pid]['blurb']}"
        if subprocess.run(["git", "commit", "-m", subject], cwd=self.root).returncode:
            raise MindError("git commit failed; index remains staged")
        branch = subprocess.run(["git", "branch", "--show-current"], cwd=self.root, text=True, capture_output=True, check=True).stdout.strip()
        if subprocess.run(["git", "push", "origin", branch], cwd=self.root).returncode:
            raise MindError(f"commit created on {branch}, but push failed")
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.root, text=True, capture_output=True, check=True).stdout.strip()
        return pid, commit, branch, replayed
