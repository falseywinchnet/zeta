from __future__ import annotations

import re


REF_RE = re.compile(r"^R0*(\d+)$", re.IGNORECASE)
CITE_RE = re.compile(r"^CITE0*(\d+)$", re.IGNORECASE)
INTERNAL_REF_RE = re.compile(r"^F(\d{6})$", re.IGNORECASE)
INTERNAL_CITE_RE = re.compile(r"^C(\d{6})$", re.IGNORECASE)


def public_id(identity):
    identity = str(identity).upper()
    match = INTERNAL_REF_RE.fullmatch(identity)
    if match:
        return f"R{int(match.group(1))}"
    match = INTERNAL_CITE_RE.fullmatch(identity)
    if match:
        return f"CITE{int(match.group(1))}"
    return identity


def internal_id(alias):
    alias = str(alias).strip()
    match = REF_RE.fullmatch(alias)
    if match:
        return f"F{int(match.group(1)):06d}"
    match = CITE_RE.fullmatch(alias)
    if match:
        return f"C{int(match.group(1)):06d}"
    if INTERNAL_REF_RE.fullmatch(alias) or INTERNAL_CITE_RE.fullmatch(alias):
        return alias.upper()
    return alias


def exact_identity(store, query):
    """Resolve a complete public or legacy identity, never a substring."""
    internal = internal_id(query)
    if internal in store.factoids:
        return {"kind": "factoid", "id": internal, "public_id": public_id(internal)}
    if internal in store.citations:
        return {"kind": "citation", "id": internal, "public_id": public_id(internal)}
    return None
