# Checks

The targeted command was run only one instance at a time from `proof/formal/`:

```sh
lake env lean ../../work/2026-07-20-cleared-jet-certificate-bridge/ClearedJetCertificateBridge.lean
```

Intermediate failures are recorded in `FAILURES.md`.  The final invocation
exited with code 0 and no warnings.

Every printed public theorem depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

A text audit found no `sorry`, `admit`, or user-declared `axiom`.  No broad
Lake rebuild or concurrent Lean process was used.
