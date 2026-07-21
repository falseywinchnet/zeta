# Theta-jet interval majorant

- Date: 2026-07-21
- Mode: advancement
- Model: OpenAI Codex
- Starting progress: P000126
- Starting boundary: the unresolved interval estimate in P000125
- Status: complete advancement candidate; kernel-checked

## Question

Can the abstract `ThetaJetControl` premise be replaced by a concrete control on
every bounded interval containing zero, using only a polynomial-times-geometric
majorant?

## Intended boundary

Prove a reusable finite-support polynomial evaluation bound, bound the recursive
theta modes uniformly on `Set.Ioo (-1) B`, construct `ThetaJetControl` for every
`B > 0`, and derive the literal theta-series derivative tower through order six.
No modular continuation or strict cleared-sign certificate is claimed here.

## Safety

Lean is compiled as a single process. The previous advancement source is copied
mechanically into this directory and extended here; the preserved P000125 work
is not edited.

## Outcome

The abstract convergence premise is discharged on every interval
`Set.Ioo (-1) B` with `B > 0`. The resulting theorem gives all six ordinary
derivative identities at every `t >= 0`. The comparison sequence is
polynomial in the positive summation index times `exp (-r*n)`, hence geometric;
no Gaussian-series, Gaussian-integral, probability, or theta-holomorphy theory
is imported.

The single-file Lean check completed with exit code zero. The artifact contains
no `sorry`, `admit`, or custom `axiom`.
