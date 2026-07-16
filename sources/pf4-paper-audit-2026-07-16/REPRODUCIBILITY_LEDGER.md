# Reproducibility ledger

## Publication-level result

The public and build PDFs are byte-identical. The LaTeX log contains no unresolved citation/reference or overfull/underfull warnings found by the audit. Visual rendering is clean.

The PDF alone is not an executable research object: it names repository-relative paths but provides no repository URL, release/archive DOI, commit, container, lockfile, or one-command replay instruction.

## Script-by-script boundary

| Script | What inspection verified it checks | What it does not replay |
|---|---|---|
| `scripts/verify_pf3_reduction.py` | Generic symbolic slope and derivative identities; two imported jet comparisons; sampled high-precision sufficiency and tail checks | It does not execute the 7,731-cell directed compact cover or a global directed tail proof |
| `scripts/verify_c4_confluent.py` | Exact moment/cumulant algebra, confluent scaling diagnostics, exact tail-margin reconstruction, sampled high-precision checks | It does not execute the 8,050-cell directed compact cover; sampled `w` checks are not global directed enclosures |
| `scripts/verify_pf4_wronskian_reduction.py` | Generic quotient identities, exact iterated-integral identities, mean splits, generic symbolic reduction, high-precision diagnostics | It relies transitively on CERT2 for global positivity; numeric spots are diagnostics only |
| `scripts/verify_pf4_transport_kernel.py` | Generic sign bridge, direct symbolic `C4` normalization, exact endpoint identity, crossing-ratio derivative, high-precision diagnostics | It relies transitively on CERT3/CERT5 for their global premises |
| `scripts/verify_continuous_pf4_separator.py` | Exact rational PF3 margin, exact central-determinant reconstruction, all 73 coefficient signs, exact spot identities, and a directed Arb discriminant | It relies transitively on the generic PF3/PF4 implication theorems |

## Verified metadata discrepancy

- The PF3 compact output states precision 192 bits; the manuscript also states 192 bits.
- `CERT2` metadata instead summarizes “Arb 256 bits; mpmath 40-60 decimal digits,” reflecting the wrapper's cross-check precision rather than the underlying compact cover.
- `CERT3` metadata lists only `mpmath` and `sympy`, although the underlying directed compact computation uses `python-flint/Arb`; the wrapper itself does not rerun that computation.

These facts make the paper's Section 12 table entries “directed and exact” misleading when read as descriptions of the named scripts. The directed base calculations exist and are content-addressed, but the named wrapper commands are audits of parts of the chain, not complete replays.

## Numerical correspondence checks

The following displayed values agree with retained certificate outputs or exact arithmetic:

- `q >= 18.7268` versus certified lower endpoint approximately `18.7268946`.
- `F2 >= 3889.2` versus certified lower endpoint approximately `3889.21527`.
- `C4 >= 2.817e7` versus certified lower endpoint approximately `2.8172286e7`.
- Cell counts 7,731 and 8,050.
- Tail example `E4 < 2082`.
- Separator margin `143/128`.
- Public/build PDF SHA-256 equality.

No displayed numerical contradiction was found in the surviving strict-PF4 or separator arguments.

## Required reproducible release

1. Archive a specific source release and give its DOI/URL and commit in the PDF.
2. Separate commands for full directed compact replay from lightweight symbolic audit commands.
3. Pin the Python, SymPy, mpmath, python-flint/Arb, and Tectonic environments in a machine-readable lock or container.
4. Publish expected hashes for base certificate outputs and the final PDF.
5. State expected wall time, memory, precision, cell count, and platform assumptions.
6. Include or generate a machine-readable manifest tying every theorem premise to its exact replay command.
