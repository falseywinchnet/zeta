# PF4 no-FLINT analytic core

- Mode: advancement
- Date: 2026-07-16
- Model: OpenAI Codex
- Question: Can the compact sign inputs `q>0`, `F2>0`, and `C4>0` for the
  Riemann kernel be proved without Arb/python-flint and, ideally, without an
  interval sweep, by closed-form identities, monotonicity, or a finite exact
  rational certificate?
- Starting MIND IDs: R141, R142, R143, R147, R149, R150, R151, R152,
  CERT2, CERT3, P000071
- Status: complete; sweep-free no-FLINT candidate proof and replay recorded

## Evidence boundary

This directory contains advancement work only. Existing MIND claims and
certificates remain unchanged. Any successful replacement proof must be
audited in a later refine round before it can supersede the Arb compact covers.

## Initial decomposition

The global PF4 theorem uses directed interval arithmetic only for the compact
sign facts on `0 <= t <= 1`:

1. `q(t)>0` and `F2(t)=q^3-(q q''-(q')^2)>0` for PF3;
2. `C4(t)>0` for the confluent order-four input.

The curvature-coordinate transport and quotient-Wronskian reductions are
exact. The region `|t|>=1` already has analytic dominant-theta tail bounds.
