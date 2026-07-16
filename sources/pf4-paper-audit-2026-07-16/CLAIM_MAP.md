# Claim map

## Scope decision

The exact-order/PF5 conclusion remains in scope. By author direction, the Michalowski citation will be removed and replaced by a hardened version of `The Riemann Kernel is Not a Polya Frequency Function of Infinite Order`. The replacement proof is treated as a conditional pre-publication boundary and is not re-audited in its current unhardened form.

## C1. Strict global PF4 for the maintained Riemann kernel

**Conclusion.** Every translation minor of orders 1 through 4 is strictly positive at strictly ordered nodes.

**Premises.**

1. The theta identity gives a real-analytic even kernel `Phi`.
2. `Phi>0`, so `ell=log Phi` is defined.
3. Certified global inequalities: `q>0`, `F2>0`, and `C4>0`.
4. `q>0` and `F2>0` imply `Lambda>0` and strict PF3 through the weighted-mean estimate.
5. Successive quotient-Wronskian identities reduce strict PF4 to `partial_xi Psi<0`.
6. The curvature coordinate gives `C4=Q^6 kappa^2 D`, hence `D>0`.
7. The endpoint transport identity gives `K=E_nu[A0]-E_mu[A0]`.
8. The density ratio has one strict crossing, so `W>0` inside the interval.
9. Therefore the transport numerator is positive, `partial_xi Psi<0`, and all fourth-order collocation minors are strictly positive.

**Evidence.** `CERT2`, `CERT3`, `CERT5`, and `CERT9`, plus Sections 2-10 and Appendices A1-A3.

**Hidden or under-exposed assumptions.**

- Positivity of `Phi` is needed before `log Phi`; it is available from evenness plus the positive-side series but is not stated in the manuscript.
- The generic quotient argument needs positivity of every denominator (`u1`, `v2`, `w3`, `Lambda`, `delta`, `kappa`); the proof chain supplies them, but the dependency is distributed across sections.
- The computer-assisted compact and tail inequalities must be independently replayable from a fixed public code release.

**Audit verdict.** The mathematical chain is coherent on the supplied record. No counterexample or sign contradiction was found. Publication readiness is blocked by evidence-boundary and exposition defects, not by an identified fatal error in this chain.

## C2. Explicit positive even Schwartz strict-PF4 separator

**Conclusion.** The seven-Gaussian mixture `f_*` is positive, even, Schwartz, and strict PF4.

**Premises.**

1. Positive mixture weights and palindromy give positivity and evenness; Gaussian decay gives Schwartz regularity.
2. Popoviciu's variance bound and the fourth-cumulant bound give `q>0` and `F2>0`.
3. The exact rational reconstruction yields a degree-72 numerator `H` with 73 positive coefficients, so `C4>0`.
4. The generic transport and quotient results from C1 then give strict PF4.

**Evidence.** Section 11, Appendix A5, and `CERT10` with transitive dependence on `CERT2`/`CERT9` for the generic implications.

**Audit verdict.** The displayed inequalities and exact reconstruction logic are internally consistent. The phrase “strict PF3 also gives kappa” is logically imprecise: it is the stronger established condition `F2>0`, not strict PF3 alone, that supplies the displayed formula and positivity.

## C3. The separator's entire Fourier transform has nonreal zeros

**Conclusion.** The Fourier transform has at least one nonreal conjugate pair of zeros.

**Premises.**

1. Gaussian translation reduces the transform to a zero-free Gaussian times a finite Laurent factor.
2. Palindromy reduces that factor to a real cubic in `u=w+w^{-1}`.
3. Directed 192-bit arithmetic proves the cubic discriminant is strictly negative.
4. A nonreal `u` cannot arise from `|w|=1`; a logarithmic lift through `w=e^{-iz}` therefore has nonzero imaginary part.

**Evidence.** Section 11.3, Appendix A5, and `CERT10`.

**Audit verdict.** Coherent and well supported locally. The abstract's statement that the computer-assisted input is confined to the Riemann-kernel `q,F2,C4` inequalities omits this directed discriminant calculation.

## C4. Continuous PF3 and PF4 membership do not force Fourier real-rootedness

**Conclusion.** Membership in either finite class is insufficient.

**Dependency.** Immediate from C2 and C3, since strict PF4 implies PF4 and PF3 membership.

**Audit verdict.** Valid if C2 and C3 hold. “Sharp” should be defined narrowly as a separator matched to order four; the paper does not prove that order five is a sufficient threshold for Fourier real-rootedness.

## C5. Exact global PF order four

**Conclusion.** Strict global PF4 plus one certified negative order-five minor gives exact global PF order four.

**Current locations.** Title, Abstract lines 4-6, Introduction lines 9 and 21-27, Section 10 title and lines 8-9, and related statements in `paper/PAPER_MAP.md`.

**Planned evidence.** A hardened version of `papers/The Riemann Kernel is Not a Polya Frequency Function of Infinite Order.pdf`, using the manuscript's kernel normalization and an explicit replayable order-five witness.

**Audit verdict.** Conditional. The logical inference is immediate, but the final paper must replace every Michalowski reference with the exact immutable hardened source and expose the witness parameters, determinant enclosure, normalization, and replay command. Acceptance cannot rely on an unpublished or moving replacement.
