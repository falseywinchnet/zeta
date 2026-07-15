from __future__ import annotations

import argparse
import sys

from .search_backend import SearchBackendError, configured_backend
from .identities import exact_identity, internal_id, public_id
from .store import MindError, Store


HELP = """MIND - local epistemic graph

Usage:
  MIND
  MIND EXPLAIN <RETRIEVE|SEARCH|ESTABLISH|CITE|CERTIFICATE|DISTINGUISH|PROGRESS|ALL>
  MIND RETRIEVE <topic-path|topic-id|R<num>|CITE<num>|CERT<num>>
  MIND SEARCH [--limit N] [--type KIND] [--explain] <terms>
  MIND ESTABLISH ...
  MIND CITE <ADD|REMOVE|LIST|CHANGE> ...
  MIND CERTIFICATE <ADD|DEL|MOD|LIST|RUN> ...
  MIND DISTINGUISH <TREE|BRANCH|PRUNE> ...
  MIND PROGRESS <RECORD|CHANGE|LIST|COMMIT> ...

Run `MIND EXPLAIN ALL` for the complete grammar. Commands are case-insensitive.
RETRIEVE is exact and causal. SEARCH accepts exact R<num>/CITE<num>/CERT<num>
identities or ordinary text across references, citations, certificates, topics, and content.
"""


EXPLANATIONS = {
    "RETRIEVE": """RETRIEVE <detail>

Detail must be one exact R<num>, CITE<num>, CERT<num>, legacy identity, topic ID, unique topic label, or full topic
path. Retrieval first finds every current standalone conclusion whose causal
closure contains a matching factoid. Each numbered TRACEMAP prints the newest
conclusion, its concise direct `because` IDs, then its oldward causal closure.
Citation and certificate supports are epistemic boundaries and are printed separately. Every
orphan TODO is appended to every retrieval. Use SEARCH when the exact identity or
topic is not yet known.
""",
    "SEARCH": """SEARCH <terms>

Searches references, citations, certificates, topic leaves, progress records, advancement files,
and lossless source records as one collection. R<num>, CITE<num>, and CERT<num> are exact
public identities and return the complete causal, citation, or certificate object without
ranking. Legacy F/C identities remain accepted.

Ordinary text combines weighted positional postings, BM25F-like saturation,
character correction, graph anchors, ConeDAG similarity, and directional
subsequence containment. Ranked output uses a hybrid secretary cutoff. If at
least eight candidates score 1/e or higher, the complete score-at-least-1/e
prefix is returned. Otherwise output stops before the first adjacent score drop
greater than 1-1/e, equivalently next/previous < 1/e. --limit remains a safety
ceiling.

  MIND SEARCH polya frequency order
  MIND SEARCH "Schoenberg, reciprocal transform"
  MIND SEARCH CITE4
  MIND SEARCH --type citation --explain author interval arithmetic

Comma segments are asymmetric. Earlier segments locate context anchors; the last
segment is the target. Targets are reranked by shortest causal or taxonomic graph
distance from anchors. --type accepts reference, citation, certificate, topic, progress, work, or
source and may repeat. --reindex is a recovery command.

The generated index is ignored by git and rebuilt automatically when missing or
stale. PROGRESS COMMIT independently rebuilds and checks it. RETRIEVE SEARCH is a SEARCH alias.
""",
    "ESTABLISH": """ESTABLISH creates or revises atomic factoids.

New:
  MIND ESTABLISH "content" RELATES <topic...>
  MIND ESTABLISH "content" BECAUSE <R... CITE... CERT...> RELATES <topic...>

An unsupported new factoid is TODO. A claim is established only when it has a
direct CITE or CERT boundary and every referenced factoid is established.

Existing:
  MIND ESTABLISH <R> REFER <R...>
  MIND ESTABLISH <R> REFER CITATION <CITE...>
  MIND ESTABLISH <R> REFER CERTIFICATE <CERT...>
  MIND ESTABLISH <R> PRUNE <direct-R...>
  MIND ESTABLISH <R> PRUNE CITATION <direct-CITE...>
  MIND ESTABLISH <R> PRUNE CERTIFICATE <direct-CERT...>
  MIND ESTABLISH <R> MODIFY [CONTENT "replacement"] [RELATES <topic...>]

CONTENT "replacement" and RELATES <topic...> may follow an existing update.
All supports must already exist. Cycles and self-support are rejected. Status
changes propagate through descendants when evidence is added or removed.
""",
    "CITE": """CITE manages independently authored external source identities.

  MIND CITE ADD --author A --body B --topic T [--paper FILE] [--artifact FILE] [--url URL]
  MIND CITE LIST [ALL|CITE1]
  MIND CITE CHANGE CITE1 [--author A] [--body B] [--topic T] [--paper FILE] [--url URL]
  MIND CITE REMOVE CITE1

ADD requires author, bibliographic body, at least one existing topic, and local
evidence through --paper or --artifact. --paper
copies the document into papers/ and records a SHA-256 checksum. --artifact records
and checksums an existing repository file without moving it. Repository-local
proofs belong in CERTIFICATE, not CITE. REMOVE refuses
to delete a citation still supporting a factoid.
""",
    "CERTIFICATE": """CERTIFICATE manages replayable internal proof boundaries.

  MIND CERTIFICATE ADD FILE --description TEXT --topic T [--command CMD]
      [--artifact FILE] [--requirement PACKAGE==VERSION] [--depends CERT]
      [--precision TEXT] [--environment DIGEST] [--timeout SECONDS]
  MIND CERTIFICATE MOD CERT1 [the same optional fields]
  MIND CERTIFICATE DEL CERT1
  MIND CERTIFICATE LIST [ALL|CERT1]
  MIND CERTIFICATE RUN [ALL|CERT1]

ADD and MOD execute the shell-free verifier command and record checksums for the
verifier, artifacts, stdout, and stderr. They also seal a readable proof manifest
whose SHA-256 transitively authenticates dependency manifests. Python files
default to `{python} FILE`. RUN forces dependency replay and verifies exact
outputs. PROGRESS COMMIT authenticates unchanged sealed manifests and replays
only missing or stale attestations before tests and commitment.
""",
    "DISTINGUISH": """DISTINGUISH manages the valid topic etymology.

  MIND DISTINGUISH TREE [topic]
  MIND DISTINGUISH BRANCH <parent> <child-label>
  MIND DISTINGUISH PRUNE [topic]

The root is math. BRANCH creates one child below an existing node. TREE prints
IDs and full hierarchy. Named PRUNE removes only an unused leaf. Bare PRUNE
removes all currently unused leaves; repeat it to remove newly exposed leaves.
""",
    "PROGRESS": """PROGRESS defines repository epochs.

  MIND PROGRESS RECORD "short blurb"
  MIND PROGRESS CHANGE <P> "corrected blurb"
  MIND PROGRESS LIST [ALL|count]
  MIND PROGRESS COMMIT

RECORD creates exactly one pending epoch. CHANGE edits only that uncommitted
record; committed history is immutable. COMMIT validates JSON, paper checksums,
causal acyclicity, replays all certificates, rebuilds the ignored search index,
compiles Python, and runs tests, then stages all changes and commits
with the progress ID, and pushes the current branch to origin. Direct git commit
and push are reserved for recovery; ordinary work uses PROGRESS COMMIT.
""",
}


def explain(name):
    name = name.upper()
    if name == "ALL":
        print("\n".join(EXPLANATIONS[key].rstrip() for key in ("RETRIEVE", "SEARCH", "ESTABLISH", "CITE", "CERTIFICATE", "DISTINGUISH", "PROGRESS")))
    elif name in EXPLANATIONS:
        print(EXPLANATIONS[name].rstrip())
    else:
        raise MindError(f"unknown command for EXPLAIN: {name}")


def split_markers(tokens, markers):
    parts, current, name = {}, [], "_"
    for token in tokens:
        upper = token.upper()
        if upper in markers:
            parts[name] = current
            name, current = upper, []
        else:
            current.append(token)
    parts[name] = current
    return parts


def cmd_establish(store, args):
    if not args:
        raise MindError("ESTABLISH requires content or a factoid ID")
    first = internal_id(args[0])
    if first in store.factoids:
        if len(args) >= 2 and args[1].upper() == "MODIFY":
            parts = split_markers(args[2:], {"CONTENT", "RELATES"})
            if parts.get("_"):
                raise MindError("MODIFY accepts only CONTENT and RELATES fields")
            content = " ".join(parts["CONTENT"]) if "CONTENT" in parts else None
            topics = parts.get("RELATES")
            store.modify_fact(first, content=content, topics=topics)
            print(f"{public_id(first)} updated; status={store.factoids[first]['status']}")
            return
        if len(args) < 3 or args[1].upper() not in ("REFER", "PRUNE"):
            raise MindError("existing factoid requires REFER, PRUNE, or MODIFY")
        action = args[1].lower()
        tail = args[2:]
        support_type = "factoid"
        if tail and tail[0].upper() in {"CITATION", "CERTIFICATE"}:
            support_type = tail[0].casefold()
            tail = tail[1:]
        parts = split_markers(tail, {"CONTENT", "RELATES"})
        refs = [internal_id(ref) for ref in parts.get("_", [])]
        if not refs:
            raise MindError(f"{action.upper()} requires at least one reference")
        content = " ".join(parts["CONTENT"]) if "CONTENT" in parts else None
        topics = parts.get("RELATES")
        store.update_fact(first, action, refs, support_type=support_type, content=content, topics=topics)
        print(f"{public_id(first)} updated; status={store.factoids[first]['status']}")
        return
    parts = split_markers(args, {"BECAUSE", "RELATES"})
    content = " ".join(parts.get("_", [])).strip()
    topics = parts.get("RELATES", [])
    because = [internal_id(ref) for ref in parts.get("BECAUSE", [])]
    fid = store.establish(content, topics, because)
    print(f"{public_id(fid)} {store.factoids[fid]['status']}")


def fact_line(store, fid):
    fact = store.factoids[fid]
    refs = " ".join(public_id(ref["id"]) for ref in fact["because"]) or "none"
    topics = ", ".join(store.topic_path(tid) for tid in fact["relates_to"])
    return f"{public_id(fid)} [{fact['status']}] {fact['content']}\n    because {refs}\n    relates-to {topics}"


def cmd_retrieve(store, detail):
    detail = internal_id(detail)
    backend = configured_backend(store)
    try:
        matches, resolved = backend.resolve(store, detail)
    except SearchBackendError as exc:
        raise MindError(str(exc)) from exc
    roots = store.retrieval_roots(matches)
    if detail in store.factoids:
        resolved = f"reference {public_id(detail)}"
    print(f"RETRIEVAL: {resolved}\nBACKEND: {backend.name}\nMATCHES: {len(matches)}\n")
    if not roots:
        print("TRACEMAPS: none")
    citation_boundaries = set()
    certificate_boundaries = set()
    for number, root in enumerate(roots, 1):
        direct = " ".join(public_id(ref["id"]) for ref in store.factoids[root]["because"]) or "none"
        print(f"TRACEMAP {number}\n{public_id(root)}: {store.factoids[root]['content']}\n  because {direct}")
        print("  TRACE")
        for fid, depth in store.trace_closure(root):
            fact = store.factoids[fid]
            refs = " ".join(public_id(ref["id"]) for ref in fact["because"]) or "none"
            print(f"    {'  ' * depth}{public_id(fid)}: {fact['content']} (because {refs})")
            citation_boundaries.update(ref["id"] for ref in fact["because"] if ref["type"] == "citation")
            certificate_boundaries.update(ref["id"] for ref in fact["because"] if ref["type"] == "certificate")
        print()
    print("EPISTEMIC BOUNDARIES")
    if citation_boundaries or certificate_boundaries:
        for cid in sorted(citation_boundaries):
            cite = store.citations[cid]
            local = f"; local={cite['paper']['path']}" if cite.get("paper") else ""
            print(f"  {public_id(cid)}: {cite['author']}. {cite['body']}{local}")
        for kid in sorted(certificate_boundaries):
            certificate = store.certificates[kid]
            print(
                f"  {public_id(kid)}: {certificate['description']}; "
                f"verifier={certificate['file']['path']}"
            )
    else:
        print("  none")
    todos = sorted((fid for fid, fact in store.factoids.items() if fact["status"] == "todo"), reverse=True)
    print("\nOPEN TODOs")
    if todos:
        for fid in todos:
            print(f"  {public_id(fid)}: {store.factoids[fid]['content']}")
    else:
        print("  none")


def cmd_search(store, args):
    parser = argparse.ArgumentParser(prog="MIND SEARCH")
    parser.add_argument("--limit", type=int, default=25)
    parser.add_argument("--type", action="append", dest="kinds")
    parser.add_argument("--explain", action="store_true")
    parser.add_argument("--reindex", action="store_true")
    parser.add_argument("query", nargs="*")
    ns = parser.parse_args(args)
    from .search_index import SearchEngine, build_index, render_results

    if ns.reindex:
        path, index = build_index(store)
        print(f"indexed {len(index['documents'])} records at {path.relative_to(store.root)}")
        if not ns.query:
            return
    query = " ".join(ns.query).strip()
    if not query:
        raise MindError("SEARCH requires terms unless --reindex is used")
    exact = exact_identity(store, query)
    if exact:
        if exact["kind"] == "factoid":
            cmd_retrieve(store, exact["id"])
        elif exact["kind"] == "citation":
            cmd_retrieve_citation(store, exact["id"])
        else:
            cmd_retrieve_certificate(store, exact["id"])
        return
    kinds = []
    for group in ns.kinds or []:
        kinds.extend(item.strip().casefold() for item in group.split(",") if item.strip())
    kind_aliases = {
        "ref": "factoid", "reference": "factoid", "cite": "citation", "cert": "certificate"
    }
    kinds = [kind_aliases.get(kind, kind) for kind in kinds]
    allowed = {"factoid", "citation", "certificate", "topic", "progress", "work", "source"}
    invalid = sorted(set(kinds) - allowed)
    if invalid:
        raise MindError(f"unknown search types: {', '.join(invalid)}")
    engine = SearchEngine(store)
    results = engine.search(query, limit=max(1, ns.limit), kinds=kinds)
    print(render_results(results, ns.explain))


def cmd_retrieve_citation(store, cid):
    cite = store.citations[cid]
    print(f"CITATION: {public_id(cid)}")
    print(f"AUTHOR: {cite['author']}")
    print(f"BODY: {cite['body']}")
    print("TOPICS: " + ", ".join(store.topic_path(tid) for tid in cite["topics"]))
    print("LOCAL EVIDENCE")
    evidence = []
    if cite.get("paper"):
        evidence.append(cite["paper"])
    evidence.extend(cite.get("artifacts", []))
    if evidence:
        for item in evidence:
            print(f"  {item['path']} sha256={item['sha256']}")
    else:
        print("  none")
    users = sorted(
        public_id(fid) for fid, fact in store.factoids.items()
        if {"type": "citation", "id": cid} in fact["because"]
    )
    print("SUPPORTS: " + (" ".join(users) if users else "none"))


def cmd_retrieve_certificate(store, kid):
    certificate = store.certificates[kid]
    print(f"CERTIFICATE: {public_id(kid)}")
    print(f"DESCRIPTION: {certificate['description']}")
    print("TOPICS: " + ", ".join(store.topic_path(tid) for tid in certificate["topics"]))
    print(f"VERIFIER: {certificate['file']['path']} sha256={certificate['file']['sha256']}")
    print("COMMAND: " + " ".join(certificate["runner"]["argv"]))
    print(f"TIMEOUT: {certificate['runner']['timeout_seconds']} seconds")
    print(f"STDOUT SHA256: {certificate['runner']['stdout_sha256']}")
    print(f"STDERR SHA256: {certificate['runner']['stderr_sha256']}")
    attestation = certificate.get("attestation")
    print("ATTESTATION: " + (
        f"{attestation['method']} manifest-sha256={attestation['manifest_sha256']} "
        f"verified={attestation['verified_at']}"
        if attestation else "unsealed; next commit will replay"
    ))
    print("DEPENDENCIES: " + (
        " ".join(public_id(dep) for dep in certificate.get("dependencies", [])) or "none"
    ))
    print("REQUIREMENTS: " + (", ".join(certificate.get("requirements", [])) or "none"))
    print(f"PRECISION: {certificate.get('precision') or 'unspecified'}")
    print(f"ENVIRONMENT: {certificate.get('environment') or 'unspecified'}")
    print("ARTIFACTS")
    if certificate.get("artifacts"):
        for item in certificate["artifacts"]:
            print(f"  {item['path']} sha256={item['sha256']}")
    else:
        print("  none")
    users = sorted(
        public_id(fid) for fid, fact in store.factoids.items()
        if {"type": "certificate", "id": kid} in fact["because"]
    )
    print("SUPPORTS: " + (" ".join(users) if users else "none"))


def citation_parser(action):
    parser = argparse.ArgumentParser(prog=f"MIND CITE {action}", add_help=True)
    if action in ("CHANGE", "REMOVE"):
        parser.add_argument("id")
    if action in ("ADD", "CHANGE"):
        parser.add_argument("--author", required=action == "ADD")
        parser.add_argument("--body", required=action == "ADD")
        parser.add_argument("--topic", action="append", dest="topics", required=action == "ADD")
        parser.add_argument("--paper")
        parser.add_argument("--artifact", action="append", dest="artifacts")
        parser.add_argument("--url")
    return parser


def cmd_cite(store, args):
    if not args:
        raise MindError("CITE requires ADD, REMOVE, LIST, or CHANGE")
    action, tail = args[0].upper(), args[1:]
    if action == "ADD":
        ns = citation_parser(action).parse_args(tail)
        cid = store.add_citation(ns.author, ns.body, ns.topics, ns.paper, ns.url, ns.artifacts)
        print(public_id(cid))
    elif action == "CHANGE":
        ns = citation_parser(action).parse_args(tail)
        cid = internal_id(ns.id)
        store.change_citation(cid, ns.author, ns.body, ns.topics, ns.paper, ns.url, ns.artifacts)
        print(f"{public_id(cid)} updated")
    elif action == "REMOVE":
        ns = citation_parser(action).parse_args(tail)
        cid = internal_id(ns.id)
        store.remove_citation(cid)
        print(f"{public_id(cid)} removed")
    elif action == "LIST":
        target = internal_id(tail[0]) if tail else "ALL"
        target = target.upper() if target.upper() == "ALL" else target
        ids = sorted(store.citations) if target == "ALL" else [target]
        for cid in ids:
            if cid not in store.citations:
                raise MindError(f"unknown citation: {cid}")
            cite = store.citations[cid]
            paths = ", ".join(store.topic_path(tid) for tid in cite["topics"])
            local = cite.get("paper", {}).get("path") if cite.get("paper") else "none"
            artifacts = ", ".join(item["path"] for item in cite.get("artifacts", [])) or "none"
            print(f"{public_id(cid)} {cite['author']}\n  {cite['body']}\n  topics: {paths}\n  paper: {local}\n  artifacts: {artifacts}")
    else:
        raise MindError(f"unknown CITE action: {action}")


def certificate_parser(action):
    parser = argparse.ArgumentParser(prog=f"MIND CERTIFICATE {action}", add_help=True)
    if action == "ADD":
        parser.add_argument("file")
    elif action == "MOD":
        parser.add_argument("id")
        parser.add_argument("--file")
    if action in {"ADD", "MOD"}:
        parser.add_argument("--description", required=action == "ADD")
        parser.add_argument("--topic", action="append", dest="topics", required=action == "ADD")
        parser.add_argument("--command")
        parser.add_argument("--artifact", action="append", dest="artifacts")
        parser.add_argument("--requirement", action="append", dest="requirements")
        parser.add_argument("--depends", action="append", dest="dependencies")
        parser.add_argument("--precision")
        parser.add_argument("--environment")
        parser.add_argument("--timeout", type=int, dest="timeout_seconds")
    return parser


def cmd_certificate(store, args):
    if not args:
        raise MindError("CERTIFICATE requires ADD, DEL, MOD, LIST, or RUN")
    aliases = {"REMOVE": "DEL", "DELETE": "DEL", "CHANGE": "MOD", "MODIFY": "MOD"}
    action = aliases.get(args[0].upper(), args[0].upper())
    tail = args[1:]
    if action == "ADD":
        ns = certificate_parser(action).parse_args(tail)
        kid = store.add_certificate(
            ns.file, ns.description, ns.topics, ns.command, ns.artifacts,
            ns.requirements, ns.precision, ns.environment,
            [internal_id(dep) for dep in ns.dependencies or []],
            ns.timeout_seconds or 300,
        )
        print(f"{public_id(kid)} added and replayed")
    elif action == "MOD":
        ns = certificate_parser(action).parse_args(tail)
        kid = internal_id(ns.id)
        store.change_certificate(
            kid, ns.file, ns.description, ns.topics, ns.command, ns.artifacts,
            ns.requirements, ns.precision, ns.environment,
            None if ns.dependencies is None else [internal_id(dep) for dep in ns.dependencies],
            ns.timeout_seconds,
        )
        print(f"{public_id(kid)} updated and replayed")
    elif action == "DEL":
        if len(tail) != 1:
            raise MindError("CERTIFICATE DEL requires one certificate ID")
        kid = internal_id(tail[0])
        store.remove_certificate(kid)
        print(f"{public_id(kid)} removed")
    elif action == "LIST":
        target = internal_id(tail[0]) if tail else "ALL"
        target = target.upper()
        ids = sorted(store.certificates) if target == "ALL" else [target]
        for kid in ids:
            if kid not in store.certificates:
                raise MindError(f"unknown certificate: {kid}")
            item = store.certificates[kid]
            print(
                f"{public_id(kid)} {item['description']}\n"
                f"  verifier: {item['file']['path']}\n"
                f"  verifier sha256: {item['file']['sha256']}\n"
                f"  manifest sha256: "
                f"{item.get('attestation', {}).get('manifest_sha256', 'unsealed')}\n"
                f"  command: {' '.join(item['runner']['argv'])}\n"
                f"  dependencies: {' '.join(public_id(dep) for dep in item.get('dependencies', [])) or 'none'}"
            )
    elif action == "RUN":
        if len(tail) > 1:
            raise MindError("CERTIFICATE RUN accepts ALL or one certificate ID")
        target = internal_id(tail[0]) if tail else "ALL"
        replayed = store.replay_certificates(target)
        print("replayed " + (" ".join(public_id(kid) for kid in replayed) or "none"))
    else:
        raise MindError(f"unknown CERTIFICATE action: {action}")


def print_tree(store, root="T000001", indent=""):
    print(f"{indent}{root} {store.topics[root]['label']}")
    children = sorted((tid for tid, item in store.topics.items() if item["parent"] == root), key=lambda tid: store.topics[tid]["label"])
    for child in children:
        print_tree(store, child, indent + "  ")


def cmd_distinguish(store, args):
    if not args:
        raise MindError("DISTINGUISH requires TREE, BRANCH, or PRUNE")
    action, tail = args[0].upper(), args[1:]
    if action == "TREE":
        root = store.resolve_topic(tail[0]) if tail else "T000001"
        if root is None:
            raise MindError(f"unknown topic: {tail[0]}")
        print_tree(store, root)
    elif action == "BRANCH":
        if len(tail) < 2:
            raise MindError("BRANCH requires parent and child label")
        tid, created = store.add_topic(tail[0], " ".join(tail[1:]))
        print(f"{tid} {'created' if created else 'exists'} {store.topic_path(tid)}")
    elif action == "PRUNE":
        removed = store.prune_topic(tail[0] if tail else None)
        print("removed " + (" ".join(removed) if removed else "none"))
    else:
        raise MindError(f"unknown DISTINGUISH action: {action}")


def cmd_progress(store, args):
    if not args:
        raise MindError("PROGRESS requires RECORD, CHANGE, LIST, or COMMIT")
    action, tail = args[0].upper(), args[1:]
    if action == "RECORD":
        pid = store.record_progress(" ".join(tail))
        print(f"{pid} recorded")
    elif action == "CHANGE":
        if len(tail) < 2:
            raise MindError("CHANGE requires progress ID and corrected blurb")
        store.change_progress(tail[0], " ".join(tail[1:]))
        print(f"{tail[0].upper()} updated")
    elif action == "LIST":
        commit_map = store.progress_commit_map()
        ids = sorted(store.progress, reverse=True)
        if tail and tail[0].upper() != "ALL":
            ids = ids[:int(tail[0])]
        for pid in ids:
            state = commit_map.get(pid, "pending")
            if state != "pending":
                state = state[:12]
            print(f"{pid} [{state}] {store.progress[pid]['blurb']}")
    elif action == "COMMIT":
        pid, commit, branch, authenticated, replayed = store.run_commit()
        print(
            f"{pid} authenticated {len(authenticated)} unchanged certificates and "
            f"replayed {len(replayed)} stale certificates, committed {commit}, "
            f"and pushed origin/{branch}"
        )
    else:
        raise MindError(f"unknown PROGRESS action: {action}")


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] in ("-h", "--help"):
        print(HELP.rstrip())
        return 0
    command, args = argv[0].upper(), argv[1:]
    try:
        if command == "EXPLAIN":
            if not args:
                raise MindError("EXPLAIN requires a command or ALL")
            explain(args[0])
            return 0
        store = Store()
        if command == "RETRIEVE":
            if not args:
                raise MindError("RETRIEVE requires one detail")
            if args[0].upper() == "SEARCH":
                cmd_search(store, args[1:])
            else:
                detail = " ".join(args)
                exact = exact_identity(store, detail)
                if exact and exact["kind"] == "citation":
                    cmd_retrieve_citation(store, exact["id"])
                elif exact and exact["kind"] == "certificate":
                    cmd_retrieve_certificate(store, exact["id"])
                else:
                    cmd_retrieve(store, detail)
        elif command == "SEARCH":
            cmd_search(store, args)
        elif command == "ESTABLISH":
            cmd_establish(store, args)
        elif command == "CITE":
            cmd_cite(store, args)
        elif command == "CERTIFICATE":
            cmd_certificate(store, args)
        elif command == "DISTINGUISH":
            cmd_distinguish(store, args)
        elif command == "PROGRESS":
            cmd_progress(store, args)
        else:
            raise MindError(f"unknown command: {command}")
        return 0
    except (MindError, ValueError) as exc:
        print(f"MIND: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
