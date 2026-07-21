# Checks

The advancement candidate is checked directly from `proof/formal` with:

```text
lake env lean ../../work/2026-07-20-terminal-quotient-psi/TerminalQuotientPsi.lean
```

This is a direct candidate check only. No maintained module or full library
rebuild was required during advancement. The final run passed and printed,
for each of the coordinate identity, terminal identity, and strict-sign
wrapper, exactly:

```text
[propext, Classical.choice, Quot.sound]
```

It printed no warning or error.
