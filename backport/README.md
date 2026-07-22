# PF4 paper backport series

The submitted paper is a frozen historical version, not the permanent best
form of the proof. The maintained Lean development has since found shorter,
more explicit routes. These should be moved into the paper in a sequence of
auditable refine rounds rather than by an undifferentiated rewrite.

## Revision rule

For each backport round:

1. name the exact Lean theorem and the manuscript claim it replaces;
2. state whether the replacement is equivalent, stronger, or merely shorter;
3. preserve any old route that still supplies useful interpretation, but move
   it out of the critical proof path;
4. rebuild the paper and its arXiv package;
5. check notation, theorem numbering, cross-references, and certificate
   provenance against the maintained Lean declarations;
6. record the submitted version and revised version as distinct releases.

## Planned rounds

1. **Proof architecture.** Make the exact Lean result
   `globalRiemannKernel_pfOrderExactly_four` the organizing theorem and expose
   its two inputs: universal strict PF4 and one exact negative PF5 minor.
2. **Analytic foundation.** Replace older exploratory derivations with the
   maintained real kernel definition, the library-backed Gaussian/Poisson
   identity, global analytic realization, parity, and exact infinite-tail
   control. State the trusted-base boundary explicitly.
3. **Fixed-order PF4 engine.** Backport
   `PF4.FixedOrderQuotientWronskian.fixedOrderFour_quotientWronskian_package`
   and the maintained fixed-size quotient-integral engine. The exact `W3`,
   three-stage `W4`, and reversed endpoint identities are `R206`--`R208` and
   `CERT29`. This is equivalent to the manuscript at the orders it uses, but
   shorter and more explicit about denominator and orientation assumptions.
   Keep arbitrary-order quotient algebra outside the critical path unless it
   adds exposition rather than proof debt.
4. **Transport route.** Backport the exported actual-kernel coordinate
   transport theorems. Keep the coordinate range honest; do not assert
   surjectivity onto all real numbers.
5. **PF5 obstruction.** Use the direct rational spacing `211/2000` witness as
   the main PF5 failure proof. Retain the confluent threshold analysis only as
   optional structure if it materially improves the paper.
6. **Final audit.** Trace every paper proposition to a maintained theorem,
   local exact certificate, or clearly named standard import. Remove stale
   symbolic-computation language and any result not used by the final proof.

## Completion

The six rounds were completed as refine epochs `P000158` through `P000163`.
The frozen submitted release is `pf4-paper-v1.0.0`/`P000074`; the revised
release is `PF4-paper-v2.0.0`/`P000163`. The exact changes and artifact hashes
are recorded in `paper/REVISION_HISTORY.md` and
`paper/RELEASE_MANIFEST.md`.

## Deprecated status group: crossing support

The former status-list group containing PO-0032 through PO-0036 is deprecated
as a required proof route. The deterministic closed coordinate-gap theorem
proves the strict gap needed by the transport integral without requiring the
right-mass, density-ratio, endpoint-limit, existence, or uniqueness-of-crossing
chain.

These five items are not false. They remain optional interpretation and an
independent measure-theoretic validation route. They must not be counted as
open blockers for exact PF order four or for the deterministic transport
closure. This advancement marks them `DEPRECATED_OPTIONAL` in the proof
ledger and adjusts the active-obligation denominator without deleting their
source files or theorem history. A later paper refine round decides how much
of that optional interpretation remains in the manuscript.

## Review-process note

A submitted paper can and normally should evolve when the authors find a
cleaner proof. During review, the revised manuscript should identify material
changes to the editor/referees, preserve the prior submission as a versioned
artifact, and avoid presenting the new proof as though it were in the original
submission. If the result and scope are unchanged, a tighter proof is usually
a strengthening of the submission. If the main theorem, hypotheses, or claimed
consequences change, the cover letter and revision summary should say so
explicitly; the journal's exact resubmission policy controls the mechanics.

The earlier SymPy work is discovery evidence, not the final trust boundary.
The backported paper should describe it that way and cite the exact Lean
theorems and replayable certificates that now carry the formal claims.
