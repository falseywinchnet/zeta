from __future__ import annotations

import hashlib
import json
import math
import re
import unicodedata
from collections import Counter, deque
from pathlib import Path

from .store import MindError, atomic_json


INDEX_VERSION = 2
INDEX_NAME = "search-index.json"
MATH_NAMES = str.maketrans({
    "∞": " infinity ", "ω": " omega ", "Ω": " omega ", "φ": " phi ",
    "Φ": " phi ", "ξ": " xi ", "Ξ": " xi ", "ζ": " zeta ",
    "λ": " lambda ", "Λ": " lambda ", "π": " pi ", "Π": " pi ",
    "θ": " theta ", "Θ": " theta ", "ρ": " rho ", "Σ": " sigma ",
})
TOKEN_RE = re.compile(r"[^\W_]+(?:[-'][^\W_]+)*", re.UNICODE)
FIELDS = ("title", "body", "topics", "links")
FIELD_WEIGHTS = {"title": 3.5, "body": 1.0, "topics": 2.4, "links": 1.8}
FIELD_B = {"title": 0.25, "body": 0.72, "topics": 0.35, "links": 0.25}
ALIASES = {
    "rh": ["riemann", "hypothesis"],
    "jc": ["jacobian", "conjecture"],
    "pf": ["polya", "frequency"],
    "pfinfinity": ["pf", "infinity"],
    "xi": ["xi"],
}
KIND_PRIOR = {"factoid": 1.0, "citation": 0.96, "work": 0.90, "topic": 0.80, "progress": 0.72, "source": 0.58}


def normalize(text):
    text = str(text).translate(MATH_NAMES).casefold()
    text = unicodedata.normalize("NFKD", text)
    return "".join(ch for ch in text if not unicodedata.combining(ch))


def tokenize(text):
    return TOKEN_RE.findall(normalize(text))


def trigrams(term):
    padded = f"^{term}$"
    return {padded[i:i + 3] for i in range(max(1, len(padded) - 2))}


def bigrams(term):
    padded = f"^{term}$"
    return {padded[i:i + 2] for i in range(max(1, len(padded) - 1))}


def damerau_levenshtein(left, right):
    rows = len(left) + 1
    cols = len(right) + 1
    distance = [[0] * cols for _ in range(rows)]
    for i in range(rows):
        distance[i][0] = i
    for j in range(cols):
        distance[0][j] = j
    for i in range(1, rows):
        for j in range(1, cols):
            cost = 0 if left[i - 1] == right[j - 1] else 1
            distance[i][j] = min(
                distance[i - 1][j] + 1,
                distance[i][j - 1] + 1,
                distance[i - 1][j - 1] + cost,
            )
            if i > 1 and j > 1 and left[i - 1] == right[j - 2] and left[i - 2] == right[j - 1]:
                distance[i][j] = min(distance[i][j], distance[i - 2][j - 2] + 1)
    return distance[-1][-1]


def _canonical_bytes(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def work_files(root):
    base = Path(root) / "work"
    allowed = {".md", ".txt", ".py", ".json", ".csv", ".tsv", ".cpp", ".hpp", ".c", ".h"}
    if not base.exists():
        return []
    return [path for path in sorted(base.rglob("*")) if path.is_file() and path.suffix.casefold() in allowed]


def source_record_files(root):
    base = Path(root) / "sources"
    return sorted(base.glob("*.turns.json")) if base.exists() else []


def source_digest(store):
    digest = hashlib.sha256()
    digest.update(f"mind-search-v{INDEX_VERSION}\0".encode())
    for name in ("factoids", "citations", "taxonomy", "progress"):
        digest.update(name.encode() + b"\0" + _canonical_bytes(store.docs[name]) + b"\0")
    for path in work_files(store.root):
        digest.update(str(path.relative_to(store.root)).encode() + b"\0")
        digest.update(path.read_bytes() + b"\0")
    for path in source_record_files(store.root):
        digest.update(str(path.relative_to(store.root)).encode() + b"\0")
        digest.update(path.read_bytes() + b"\0")
    return digest.hexdigest()


def _documents(store):
    docs = []
    for fid, fact in sorted(store.factoids.items()):
        docs.append({
            "id": fid, "kind": "factoid", "title": fid,
            "body": fact["content"],
            "topics": " ".join(store.topic_path(tid) for tid in fact["relates_to"]),
            "links": " ".join(ref["id"] for ref in fact["because"]),
            "status": fact["status"],
        })
    for cid, cite in sorted(store.citations.items()):
        artifacts = [item["path"] for item in cite.get("artifacts", [])]
        if cite.get("paper"):
            artifacts.append(cite["paper"]["path"])
        docs.append({
            "id": cid, "kind": "citation", "title": cite["author"],
            "body": cite["body"],
            "topics": " ".join(store.topic_path(tid) for tid in cite["topics"]),
            "links": " ".join(artifacts + ([cite["source_url"]] if cite.get("source_url") else [])),
            "status": "boundary",
        })
    for tid in sorted(store.topics):
        item = store.topics[tid]
        docs.append({
            "id": tid, "kind": "topic", "title": item["label"],
            "body": store.topic_path(tid), "topics": store.topic_path(tid),
            "links": item["parent"] or "", "status": "taxonomy",
        })
    commits = store.progress_commit_map()
    for pid, item in sorted(store.progress.items()):
        docs.append({
            "id": pid, "kind": "progress", "title": pid, "body": item["blurb"],
            "topics": "progress", "links": commits.get(pid, "pending"),
            "status": "recorded",
        })
    for path in work_files(store.root):
        relative = str(path.relative_to(store.root))
        try:
            body = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        docs.append({
            "id": "W" + hashlib.sha256(relative.encode()).hexdigest()[:12].upper(),
            "kind": "work", "title": relative,
            "body": body, "topics": "work " + " ".join(path.parts[1:-1]),
            "links": relative, "status": "raw",
        })
    for path in source_record_files(store.root):
        relative = str(path.relative_to(store.root))
        try:
            source = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        for record in source.get("records", []):
            sequence = record.get("sequence")
            role = record.get("role", "record")
            stable = hashlib.sha256(f"{relative}:{sequence}".encode()).hexdigest()[:12].upper()
            docs.append({
                "id": "S" + stable, "kind": "source",
                "title": f"{relative}#{sequence} {role}",
                "body": record.get("body", ""), "topics": "source conversation raw",
                "links": f"{relative}#{sequence}", "status": "raw",
            })
    return docs


def _graph(store, docs):
    adjacency = {doc["id"]: set() for doc in docs}

    def edge(left, right):
        if left in adjacency and right in adjacency:
            adjacency[left].add(right)
            adjacency[right].add(left)

    for fid, fact in store.factoids.items():
        for ref in fact["because"]:
            edge(fid, ref["id"])
        for tid in fact["relates_to"]:
            edge(fid, tid)
    for cid, cite in store.citations.items():
        for tid in cite["topics"]:
            edge(cid, tid)
    for tid, item in store.topics.items():
        if item["parent"]:
            edge(tid, item["parent"])
    return {key: sorted(value) for key, value in adjacency.items()}


def build_index(store):
    documents = _documents(store)
    postings = {}
    totals = {field: 0 for field in FIELDS}
    vocabulary = set()
    for doc_index, doc in enumerate(documents):
        doc["terms"] = {}
        stream = []
        for field in FIELDS:
            tokens = tokenize(doc[field])
            totals[field] += len(tokens)
            stream.extend(tokens)
            counts = Counter(tokens)
            doc["terms"][field] = dict(sorted(counts.items()))
            for term in counts:
                postings.setdefault(term, []).append(doc_index)
                vocabulary.add(term)
        doc["stream"] = stream
    count = max(1, len(documents))
    averages = {field: totals[field] / count for field in FIELDS}
    trigram_map = {}
    bigram_map = {}
    for term in sorted(vocabulary):
        for gram in trigrams(term):
            trigram_map.setdefault(gram, []).append(term)
        for gram in bigrams(term):
            bigram_map.setdefault(gram, []).append(term)
    index = {
        "version": INDEX_VERSION,
        "source_digest": source_digest(store),
        "documents": documents,
        "postings": {term: sorted(set(ids)) for term, ids in sorted(postings.items())},
        "trigrams": {gram: terms for gram, terms in sorted(trigram_map.items())},
        "bigrams": {gram: terms for gram, terms in sorted(bigram_map.items())},
        "averages": averages,
        "graph": _graph(store, documents),
    }
    path = store.data_dir / INDEX_NAME
    atomic_json(path, index)
    return path, index


def load_index(store, require_current=True):
    path = store.data_dir / INDEX_NAME
    if not path.is_file():
        raise MindError("search index missing; run MIND SEARCH --reindex or PROGRESS RECORD")
    try:
        index = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise MindError(f"cannot load search index: {exc}") from exc
    if index.get("version") != INDEX_VERSION:
        raise MindError("search index version mismatch; rebuild it")
    if require_current and index.get("source_digest") != source_digest(store):
        raise MindError("search index is stale; record progress or explicitly reindex")
    return index


def index_is_current(store):
    try:
        load_index(store, require_current=True)
        return True
    except MindError:
        return False


class SearchEngine:
    def __init__(self, store):
        self.store = store
        self.index = load_index(store)
        self.docs = self.index["documents"]
        self.N = max(1, len(self.docs))

    def _expanded_terms(self, query_term):
        terms = {query_term: 1.0}
        for alias in ALIASES.get(query_term, []):
            terms[alias] = max(terms.get(alias, 0), 0.82)
        vocab = self.index["postings"]
        if query_term in vocab:
            return terms
        for term in vocab:
            if len(query_term) >= 3 and term.startswith(query_term):
                terms[term] = max(terms.get(term, 0), 0.78)
        grams = trigrams(query_term)
        candidates = set()
        for gram in grams:
            candidates.update(self.index["trigrams"].get(gram, []))
        for gram in bigrams(query_term):
            candidates.update(self.index["bigrams"].get(gram, []))
        for term in candidates:
            other = trigrams(term)
            similarity = len(grams & other) / max(1, len(grams | other))
            threshold = 0.34 if len(query_term) >= 5 else 0.55
            if similarity >= threshold:
                terms[term] = max(terms.get(term, 0), 0.68 * similarity)
        if len(query_term) >= 4:
            for term in candidates:
                if abs(len(term) - len(query_term)) > 2:
                    continue
                similarity = 1 - damerau_levenshtein(query_term, term) / max(len(query_term), len(term))
                if similarity >= 0.68:
                    terms[term] = max(terms.get(term, 0), 0.72 * similarity)
        return terms

    def _segment_scores(self, segment):
        query_tokens = tokenize(segment)
        scores = {}
        details = {}
        k1 = 1.2
        for raw in query_tokens:
            for term, expansion_weight in self._expanded_terms(raw).items():
                posting = self.index["postings"].get(term, [])
                if not posting:
                    continue
                df = len(posting)
                idf = math.log(1 + (self.N - df + 0.5) / (df + 0.5))
                for doc_index in posting:
                    doc = self.docs[doc_index]
                    weighted_tf = 0.0
                    for field in FIELDS:
                        tf = doc["terms"][field].get(term, 0)
                        if not tf:
                            continue
                        length = sum(doc["terms"][field].values())
                        average = max(0.1, self.index["averages"][field])
                        norm = 1 - FIELD_B[field] + FIELD_B[field] * length / average
                        weighted_tf += FIELD_WEIGHTS[field] * tf / norm
                    value = expansion_weight * idf * (k1 + 1) * weighted_tf / (k1 + weighted_tf)
                    scores[doc_index] = scores.get(doc_index, 0.0) + value
                    details.setdefault(doc_index, []).append((raw, term, value))
        normalized_segment = " ".join(query_tokens)
        for doc_index in list(scores):
            doc = self.docs[doc_index]
            stream = doc["stream"]
            if query_tokens and any(stream[i:i + len(query_tokens)] == query_tokens for i in range(len(stream) - len(query_tokens) + 1)):
                scores[doc_index] += 1.6
                details[doc_index].append((normalized_segment, "exact-phrase", 1.6))
            if normalize(segment).strip() == normalize(doc["id"]).strip():
                scores[doc_index] += 20.0
                details[doc_index].append((segment, "exact-id", 20.0))
        return scores, details

    def _distances(self, seed_ids, limit=7):
        graph = self.index["graph"]
        distance = {ident: 0 for ident in seed_ids}
        queue = deque(seed_ids)
        while queue:
            node = queue.popleft()
            if distance[node] >= limit:
                continue
            for neighbor in graph.get(node, []):
                if neighbor not in distance:
                    distance[neighbor] = distance[node] + 1
                    queue.append(neighbor)
        return distance

    def search(self, query, limit=10, kinds=None):
        segments = [part.strip() for part in query.split(",") if part.strip()]
        if not segments:
            raise MindError("SEARCH requires at least one term")
        segment_data = [self._segment_scores(segment) for segment in segments]
        target_scores, target_details = segment_data[-1]
        if not target_scores and len(segment_data) > 1:
            target_scores = dict(segment_data[0][0])
            target_details = dict(segment_data[0][1])
        scores = dict(target_scores)
        explanations = {idx: {"lexical": score, "anchors": []} for idx, score in scores.items()}
        for anchor_index, (anchor_scores, _) in enumerate(segment_data[:-1]):
            seeds = [self.docs[idx]["id"] for idx, _ in sorted(anchor_scores.items(), key=lambda item: item[1], reverse=True)[:8]]
            distances = self._distances(seeds) if seeds else {}
            for doc_index in list(scores):
                ident = self.docs[doc_index]["id"]
                if ident in distances:
                    bonus = 3.2 / (1 + distances[ident])
                    scores[doc_index] += bonus
                    explanations[doc_index]["anchors"].append({
                        "segment": segments[anchor_index], "distance": distances[ident], "bonus": bonus,
                    })
                if doc_index in anchor_scores:
                    direct = min(2.0, anchor_scores[doc_index] * 0.25)
                    scores[doc_index] += direct
                    explanations[doc_index]["anchors"].append({
                        "segment": segments[anchor_index], "distance": 0, "bonus": direct,
                    })
        allowed = set(kinds or [])
        ranked = []
        for doc_index, score in scores.items():
            doc = self.docs[doc_index]
            if allowed and doc["kind"] not in allowed:
                continue
            score *= KIND_PRIOR.get(doc["kind"], 1.0)
            ranked.append({
                "score": score, "document": doc,
                "matches": target_details.get(doc_index, []),
                "explain": explanations.get(doc_index, {"lexical": score, "anchors": []}),
            })
        ranked.sort(key=lambda item: (-item["score"], item["document"]["id"]))
        return ranked[:limit]


def render_results(results, explain=False):
    if not results:
        return "SEARCH RESULTS: none"
    lines = []
    for number, result in enumerate(results, 1):
        doc = result["document"]
        body = " ".join(doc["body"].split())
        if len(body) > 220:
            body = body[:217] + "..."
        lines.append(f"{number}. {doc['id']} [{doc['kind']}/{doc['status']}] score={result['score']:.4f}")
        if doc["title"] != doc["id"]:
            lines.append(f"   {doc['title']}")
        lines.append(f"   {body}")
        if doc["topics"]:
            lines.append(f"   in {doc['topics']}")
        if explain:
            matches = ", ".join(f"{raw}->{term}:{value:.2f}" for raw, term, value in result["matches"][:8]) or "none"
            lines.append(f"   lexical {result['explain']['lexical']:.4f}; matches {matches}")
            for anchor in result["explain"]["anchors"]:
                lines.append(f"   anchor {anchor['segment']!r} distance={anchor['distance']} bonus={anchor['bonus']:.3f}")
    return "\n".join(lines)
