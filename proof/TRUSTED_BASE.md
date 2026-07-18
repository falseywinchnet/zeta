# Trusted base

Status: incomplete; formal proof not yet claimed.

## Intended final trusted base

- Lean 4 kernel `v4.32.0`, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Lake `5.0.0-src+8c9756b`.
- mathlib `v4.32.0`, resolved commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lean foundational axioms actually reported by `#print axioms`.
- Any explicitly accepted classical axioms used by mathlib.

## Current conventional/certificate base

- CPython and the standard library for certificate replay.
- SymPy 1.14.0 for current exact symbolic generators/verifiers.
- Exact rational arithmetic and the mathematical soundness of each verifier's
  implementation.
- Local source files and checksums registered by MIND certificates.

These items support current `CERTIFIED` claims; they are not yet connected to
Lean theorems. Output hashes certify reproducibility only.

## Forbidden implicit trust

- comments or prose assertions;
- positivity assumptions attached to fresh CAS symbols;
- floating-point sign decisions;
- undeclared Lean axioms;
- `sorry`, `admit`, or equivalent placeholders;
- unchecked foreign-function results;
- theorem names without exact statements and versions;
- the submitted paper as an oracle.

## Open foundation decisions

1. Decide whether certificates are replayed entirely in Lean or through a
   minimal external checker plus a declared trust bridge.
2. Record whether quotient/integral arguments require classical choice,
   quotient soundness, or additional measure-theory imports.
3. Define the clean-build environment and reproducibility boundary.
