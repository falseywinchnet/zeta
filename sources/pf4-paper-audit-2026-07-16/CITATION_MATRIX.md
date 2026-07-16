# Citation and literature matrix

## Explicit citations

| Manuscript use | Supplied source | Support verdict |
|---|---|---|
| Definition/background for TP/TN and Schoenberg characterization | Belton, Guillot, Khare, Putinar, arXiv:2110.08206 | Supported. The supplied PDF defines TP/TN/TNp and states Schoenberg's bilateral-Laplace-transform theorem. It is a modern overview, not a substitute for all foundational and finite-order literature. |
| PF5/exact-order branch in the audited PDF | Michalowski, arXiv:2602.20313 | Slated for removal by author direction; no further assessment included. |
| Planned PF5/exact-order replacement | Hardened `The Riemann Kernel is Not a Polya Frequency Function of Infinite Order` | Conditional. The local draft uses the same kernel normalization, but the final hardened version, immutable locator, and replay boundary are not yet present in the audited PDF. |

## Verified citation gaps in the supplied corpus

1. **Finite-order PF/TN characterization.** Khare's `Multiply Positive Functions...` states a characterization of TNp functions for `p>=3` (Theorem E). The repository's own PF3 proof record cites it as an independent implication, but the manuscript does not.
2. **Riemann-kernel/Fourier-Wronskian literature.** Dimitrov and Xu explicitly give the same Riemann-kernel normalization used by the manuscript and study Fourier/Laplace Wronskians and real-zero criteria. The manuscript's Wronskian and Fourier framing does not cite it.
3. **Riemann-kernel normalization and de Bruijn-Newman context.** The kernel is called classical without a direct source for its normalization or its Fourier relation to Xi.
4. **Named Popoviciu inequality.** Section 11 invokes it without citation.
5. **Computer-assisted proof standards.** No citation or statement of a recognized reproducibility standard accompanies the interval proof.
6. **Contrary and adjacent literature.** The introduction does not explain how this result differs from moment-inequality, Jensen-polynomial, de Bruijn-Newman, or finite-order total-positivity approaches already present in the supplied library.

## Originality status

The local corpus is insufficient to establish originality, and no comprehensive priority search was supplied.

Before publication, a human literature review should check MathSciNet, zbMATH, Crossref, Google Scholar citation graphs, and current arXiv full text for:

- finite-order total positivity of the Riemann/de Bruijn-Newman kernel;
- quotient-Wronskian criteria for TP4 translation kernels;
- positive even Schwartz PF4 kernels with nonreal Fourier zeros;
- existing stochastic-order/transport representations of fourth-order minors.

The manuscript should make a precise originality claim only after that search and should distinguish new identities from repackaged classical Chebyshev-system or total-positivity machinery.
