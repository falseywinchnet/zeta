from __future__ import annotations

import argparse
import sys

from .search_backend import SearchBackendError, configured_backend
from .store import MindError, Store


HELP = """MIND - local epistemic graph

Usage:
  MIND
  MIND EXPLAIN <RETRIEVE|SEARCH|ESTABLISH|CITE|DISTINGUISH|PROGRESS|ALL>
  MIND RETRIEVE <topic-path|topic-id|factoid-id>
  MIND SEARCH [--limit N] [--type KIND] [--explain] <terms>
  MIND ESTABLISH ...
  MIND CITE <ADD|REMOVE|LIST|CHANGE> ...
  MIND DISTINGUISH <TREE|BRANCH|PRUNE> ...
  MIND PROGRESS <RECORD|CHANGE|LIST|COMMIT> ...

Run `MIND EXPLAIN ALL` for the complete grammar. Commands are case-insensitive.
RETRIEVE is exact and causal. SEARCH is lexical, typo-tolerant, positional, and
graph-contextual; comma-separated terms use earlier segments as context anchors.
"""


EXPLANATIONS = {
    "RETRIEVE": """RETRIEVE <detail>

Detail must be one exact factoid ID, topic ID, unique topic label, or full topic
path. Retrieval first finds every current standalone conclusion whose causal
closure contains a matching factoid. Each numbered TRACEMAP prints the newest
conclusion, its concise direct `because` IDs, then its oldward causal closure.
Citation supports are epistemic boundaries and are printed separately. Every
orphan TODO is appended to every retrieval. Use SEARCH when the exact identity or
topic is not yet known.
""",
    "SEARCH": """SEARCH <terms>

Searches factoids, citations, topics, progress records, advancement files, and
lossless source records.
The static index uses weighted positional postings, BM25F-like saturation,
character-trigram correction, aliases, exact IDs, and phrase proximity.

  MIND SEARCH polya frequency order
  MIND SEARCH "Schoenberg, reciprocal transform"
  MIND SEARCH --type citation --explain author interval arithmetic

Comma segments are asymmetric. Earlier segments locate context anchors; the last
segment is the target. Targets are reranked by shortest causal or taxonomic graph
distance from anchors. --type accepts factoid, citation, topic, progress, work, or
source and may repeat. --reindex is a recovery command.

SEARCH refuses a stale index. PROGRESS RECORD rebuilds it; PROGRESS COMMIT checks
that no indexed source changed afterward. RETRIEVE SEARCH is a SEARCH alias.
""",
    "ESTABLISH": """ESTABLISH creates or revises atomic factoids.

New:
  MIND ESTABLISH "content" RELATES <topic...>
  MIND ESTABLISH "content" BECAUSE <F...> RELATES <topic...>

An unsupported new factoid is TODO. BECAUSE accepts existing factoids only.

Existing:
  MIND ESTABLISH <F> REFER <F...>
  MIND ESTABLISH <F> REFER CITATION <C...>
  MIND ESTABLISH <F> PRUNE <direct-F...>
  MIND ESTABLISH <F> PRUNE CITATION <direct-C...>

CONTENT "replacement" and RELATES <topic...> may follow an existing update.
All references must already exist. Cycles and self-support are rejected. Removing
the last support returns a factoid to TODO.
""",
    "CITE": """CITE manages source identities at the epistemic boundary.

  MIND CITE ADD --author A --body B --topic T [--paper FILE] [--artifact FILE] [--url URL]
  MIND CITE LIST [ALL|C000001]
  MIND CITE CHANGE C000001 [--author A] [--body B] [--topic T] [--paper FILE] [--url URL]
  MIND CITE REMOVE C000001

ADD requires author, bibliographic body, and at least one existing topic. --paper
copies the document into papers/ and records a SHA-256 checksum. --artifact records
and checksums an existing repository file without moving it. REMOVE refuses
to delete a citation still supporting a factoid.
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

RECORD creates exactly one pending epoch and rebuilds the search index. CHANGE edits only that uncommitted
record; committed history is immutable. COMMIT validates JSON, paper checksums,
causal acyclicity, Python compilation, and tests, then stages all changes, commits
with the progress ID, and pushes the current branch to origin. Direct git commit
and push are reserved for recovery; ordinary work uses PROGRESS COMMIT.
""",
}


def explain(name):
    name = name.upper()
    if name == "ALL":
        print("\n".join(EXPLANATIONS[key].rstrip() for key in ("RETRIEVE", "SEARCH", "ESTABLISH", "CITE", "DISTINGUISH", "PROGRESS")))
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
    first = args[0].upper()
    if first in store.factoids:
        if len(args) < 3 or args[1].upper() not in ("REFER", "PRUNE"):
            raise MindError("existing factoid requires REFER or PRUNE")
        action = args[1].lower()
        tail = args[2:]
        citation = bool(tail and tail[0].upper() == "CITATION")
        if citation:
            tail = tail[1:]
        parts = split_markers(tail, {"CONTENT", "RELATES"})
        refs = parts.get("_", [])
        if not refs:
            raise MindError(f"{action.upper()} requires at least one reference")
        content = " ".join(parts["CONTENT"]) if "CONTENT" in parts else None
        topics = parts.get("RELATES")
        store.update_fact(first, action, refs, citation=citation, content=content, topics=topics)
        print(f"{first} updated; status={store.factoids[first]['status']}")
        return
    parts = split_markers(args, {"BECAUSE", "RELATES"})
    content = " ".join(parts.get("_", [])).strip()
    topics = parts.get("RELATES", [])
    because = parts.get("BECAUSE", [])
    fid = store.establish(content, topics, because)
    print(f"{fid} {store.factoids[fid]['status']}")


def fact_line(store, fid):
    fact = store.factoids[fid]
    refs = " ".join(ref["id"] for ref in fact["because"]) or "none"
    topics = ", ".join(store.topic_path(tid) for tid in fact["relates_to"])
    return f"{fid} [{fact['status']}] {fact['content']}\n    because {refs}\n    relates-to {topics}"


def cmd_retrieve(store, detail):
    backend = configured_backend(store)
    try:
        matches, resolved = backend.resolve(store, detail)
    except SearchBackendError as exc:
        raise MindError(str(exc)) from exc
    roots = store.retrieval_roots(matches)
    print(f"RETRIEVAL: {resolved}\nBACKEND: {backend.name}\nMATCHES: {len(matches)}\n")
    if not roots:
        print("TRACEMAPS: none")
    boundaries = set()
    for number, root in enumerate(roots, 1):
        direct = " ".join(ref["id"] for ref in store.factoids[root]["because"]) or "none"
        print(f"TRACEMAP {number}\n{root}: {store.factoids[root]['content']}\n  because {direct}")
        print("  TRACE")
        for fid, depth in store.trace_closure(root):
            fact = store.factoids[fid]
            refs = " ".join(ref["id"] for ref in fact["because"]) or "none"
            print(f"    {'  ' * depth}{fid}: {fact['content']} (because {refs})")
            boundaries.update(ref["id"] for ref in fact["because"] if ref["type"] == "citation")
        print()
    print("EPISTEMIC BOUNDARIES")
    if boundaries:
        for cid in sorted(boundaries):
            cite = store.citations[cid]
            local = f"; local={cite['paper']['path']}" if cite.get("paper") else ""
            print(f"  {cid}: {cite['author']}. {cite['body']}{local}")
    else:
        print("  none")
    todos = sorted((fid for fid, fact in store.factoids.items() if fact["status"] == "todo"), reverse=True)
    print("\nOPEN TODOs")
    if todos:
        for fid in todos:
            print(f"  {fid}: {store.factoids[fid]['content']}")
    else:
        print("  none")


def cmd_search(store, args):
    parser = argparse.ArgumentParser(prog="MIND SEARCH")
    parser.add_argument("--limit", type=int, default=10)
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
    kinds = []
    for group in ns.kinds or []:
        kinds.extend(item.strip().casefold() for item in group.split(",") if item.strip())
    allowed = {"factoid", "citation", "topic", "progress", "work", "source"}
    invalid = sorted(set(kinds) - allowed)
    if invalid:
        raise MindError(f"unknown search types: {', '.join(invalid)}")
    engine = SearchEngine(store)
    results = engine.search(query, limit=max(1, ns.limit), kinds=kinds)
    print(render_results(results, ns.explain))


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
        print(cid)
    elif action == "CHANGE":
        ns = citation_parser(action).parse_args(tail)
        store.change_citation(ns.id, ns.author, ns.body, ns.topics, ns.paper, ns.url, ns.artifacts)
        print(f"{ns.id.upper()} updated")
    elif action == "REMOVE":
        ns = citation_parser(action).parse_args(tail)
        store.remove_citation(ns.id)
        print(f"{ns.id.upper()} removed")
    elif action == "LIST":
        target = tail[0].upper() if tail else "ALL"
        ids = sorted(store.citations) if target == "ALL" else [target]
        for cid in ids:
            if cid not in store.citations:
                raise MindError(f"unknown citation: {cid}")
            cite = store.citations[cid]
            paths = ", ".join(store.topic_path(tid) for tid in cite["topics"])
            local = cite.get("paper", {}).get("path") if cite.get("paper") else "none"
            artifacts = ", ".join(item["path"] for item in cite.get("artifacts", [])) or "none"
            print(f"{cid} {cite['author']}\n  {cite['body']}\n  topics: {paths}\n  paper: {local}\n  artifacts: {artifacts}")
    else:
        raise MindError(f"unknown CITE action: {action}")


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
        pid, commit, branch = store.run_commit()
        print(f"{pid} committed {commit} and pushed origin/{branch}")
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
                cmd_retrieve(store, " ".join(args))
        elif command == "SEARCH":
            cmd_search(store, args)
        elif command == "ESTABLISH":
            cmd_establish(store, args)
        elif command == "CITE":
            cmd_cite(store, args)
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
