# Proof system specifications

## 0. Purpose and scope

This directory is the proof-development layer. It is separate from the
submitted paper. The submitted paper is an immutable reference artifact for
this project unless a later, explicit publication decision changes that rule.
Proof work may expand, reorganize, simplify, or formalize its arguments without
silently editing the paper or claiming that the formal development already
exists.

This specification is theorem-independent. A particular theorem is an
*instance* of the system and must be declared in `TARGET.md`. The present PF4
classification may be the first instance, but its notation and proof shape do
not define the general standard.

The governing criterion is:

> A theorem is complete only when its exact conclusion follows from explicit,
> jointly satisfiable premises by a kernel-checkable chain of deductions
> covering every value admitted by its quantifiers. No covered counterexample
> can then exist without contradicting a checked premise, deduction, or named
> foundation.

Testing, symbolic simplification, exact arithmetic, certificate replay,
publication, peer review, and agreement among people or models are useful
evidence. None is automatically a proof of the mathematical statement encoded
around it.

## 1. Separation of artifacts

The project maintains four distinct objects:

1. **Submitted paper** — the already submitted exposition. It is not revised by
   work governed by this specification.
2. **Expanded proof** — a readable, section-aligned derivation in which every
   compressed “because” is recursively expanded.
3. **Certificates and verifiers** — exact finite evidence checked by narrowly
   scoped programs.
4. **Lean 4 development** — the final kernel-checked dependency chain.

No status transfers automatically between these objects. In particular, a
sentence in the paper is not a Lean theorem, and a successful certificate is
not a proof of the theorem that a caller intended unless the certificate's
checked statement is formally connected to that theorem.

## 2. Exact target contract

Each proof instance begins with one immutable target record containing:

- the theorem's exact formal statement;
- every quantifier and its order;
- the type and domain of every variable;
- all regularity, ordering, nonvanishing, convergence, and normalization
  hypotheses;
- the definitions of all named objects;
- boundary, endpoint, degenerate, and confluent cases;
- the intended strict or weak conclusion;
- explicit non-goals;
- the source section or claim being reconstructed;
- the condition that would constitute a counterexample.

Changing any item creates a new target version. A later proof file may not
silently strengthen the assumptions, shrink the domain, weaken strictness, or
replace the conclusion by a nearby statement.

For the current project, `TARGET.md` should eventually give separate theorem
records for the positive PF4 result, lower-order consequences, the order-five
obstruction, and any claimed exact-order classification. Their conjunction is
not assumed merely because the paper discusses them together.

## 3. Non-vacuity policy

### 3.1 What counts as vacuous

A proof step is vacuous for this project if it obtains a target conclusion only
because:

- the hypotheses are inconsistent;
- the quantified domain is empty;
- existence, positivity, ordering, normalization, convergence, or
  nonvanishing was inserted as an assumption when it was an obligation;
- the conclusion was encoded into a variable's type, constructor, subtype, or
  local axiom and then read back;
- an implication's antecedent was never connected to the objects in the target
  theorem;
- a checker verifies only that two user-supplied expressions agree, without
  proving that either expression denotes the required mathematical object;
- a universal claim is replaced by finitely many samples;
- an error branch, unreachable branch, contradictory interval, or empty case
  split closes the goal;
- the formal theorem has stronger hypotheses or a weaker conclusion than the
  declared target.

Logically valid implications with impossible antecedents may be useful facts,
but they cannot discharge a theorem-instance obligation unless antecedent
satisfiability and the instance map are proved.

### 3.2 Mandatory non-vacuity checks

Every theorem-bearing obligation must record and check:

1. **Inhabitation:** the quantified domain and each constrained configuration
   are nonempty, or the theorem explicitly and intentionally handles an empty
   case.
2. **Consistency by construction:** concrete objects satisfying the local
   hypotheses are constructed from earlier definitions whenever those
   hypotheses are not part of the public target.
3. **Assumption provenance:** every hypothesis is either in the target contract
   or is derived by a named prior obligation.
4. **Object identity:** the expression checked is definitionally equal or
   theorem-proved equal to the object appearing in the target.
5. **Quantifier coverage:** all branches, endpoints, degeneracies, signs, and
   orderings admitted by the target are covered.
6. **Strictness source:** every strict inequality names the positive quantity,
   nonzero witness, positive-length interval, or other fact preventing equality.
7. **Counterexample interface:** the obligation states a concrete refutation
   condition and explains which checked step excludes it.

The audit must try to instantiate the premises independently. “Lean accepted
the implication” is not sufficient if the antecedent is uninhabited or detached
from the target instance.

### 3.3 Illustrative failure: a density ratio

Suppose a local computation contains

```python
ratio = C * (z - y) / (y - p)
derivative = sp.factor(sp.diff(ratio, y))
stated = -C * (z - p) / (y - p) ** 2
assert sp.factor(derivative - stated) == 0
```

This establishes only a formal rational-function identity in the CAS encoding.
It does **not** establish any of the following:

- `p < y < z` or `p < z`;
- `C > 0`;
- nonvanishing of `y - p`;
- that `ratio` is the ratio of the required densities;
- existence or normalization of those densities;
- strict decrease on the required interval;
- endpoint limits, existence and uniqueness of a crossing, or positivity of a
  CDF gap.

Likewise,

```python
Wz = sp.symbols("Wz", positive=True)
assert Wz > 0
```

proves nothing about the endpoint value of a previously defined function `W`.
It only asks the symbolic system to repeat a supplied assumption about a new
symbol.

A non-vacuous proof must instead define the measures and `W`, prove their
normalization and support, derive the ratio formula on a nonempty interval,
prove its denominator and sign conditions, derive the endpoint limits, obtain
the unique crossing, prove the sign pattern of `W'`, and derive strict endpoint
or tail mass from a positive density on a positive-length set. Only then may
the resulting positivity theorem be used downstream.

## 4. Expanded-because proof

### 4.1 Section frames

The readable proof evolves as a collection of *section frames*. Each frame is
associated with exactly one stable section or claim in the proof being
reconstructed. For the current paper these anchors should use stable IDs such
as `S02`, `S05`, `S08`, `S09`, and `S10`, not displayed section numbers that
may change.

Each frame records:

- `Frame ID`;
- source section and exact claim span;
- exact proposition proved by the frame;
- definitions introduced or used;
- quantified variables and domains;
- hypotheses and their provenance;
- conclusion;
- a numbered deduction;
- every immediate “because” dependency;
- imported results and certificate boundaries;
- non-vacuity witness;
- counterexample condition;
- unresolved edges;
- conventional and formal status.

The frame boundary prevents a polished explanation in one section from being
mistaken for support of a different claim.

### 4.2 Recursive expansion rule

For every inferential sentence of the form “claim A because B,” create an edge
`A -> B` and give `B` its exact proposition. Expand `B` in the same way until
the leaf is one of:

1. a Lean theorem checked without placeholders;
2. a certificate whose mathematical statement is checked and whose soundness
   bridge is proved or explicitly trusted;
3. an imported formal theorem with an exact statement and hypothesis map;
4. a named foundational axiom or definition;
5. an explicitly unresolved obligation.

An unresolved leaf remains a gap. Citation, familiarity, or the phrase
“standard result” does not close it.

### 4.3 Transitive literature closure

When a paper is relied upon, record the exact theorem, page or stable locator,
edition/version, hypotheses, and the local substitution proving that its
hypotheses apply. Then inspect the dependencies used by that theorem. Repeat
this process for supporting papers, and for papers supporting those papers,
unless a usable formal proof of the exact result is found.

“Continue to infinity” is implemented as a least-fixed-point traversal of the
reachable dependency graph:

- expand every newly discovered theorem-bearing edge;
- preserve cycles as strongly connected components rather than recursing
  forever;
- deduplicate identical theorem/version records;
- stop a branch only at a formal proof, declared foundation, checked
  certificate boundary, or visible unresolved import;
- rerun the traversal whenever a source, version, or dependency changes.

The graph may remain open-ended as scholarship develops. Completion is claimed
only when the target's reachable subgraph has no unresolved theorem-bearing
leaves. Bibliographic context that is not used inferentially is recorded but
does not enter the proof dependency closure.

### 4.4 Evidence retention

Every cited paper must be preserved under `papers/` with a checksum, consistent
with repository evidence rules. External URLs are locators, not evidence
substitutes. Exact quotations are not required when a precise theorem statement
and locator suffice, but the original source bytes must remain available.

## 5. Proof graph model

The canonical graph uses typed nodes and edges.

Node types:

- `TARGET`
- `CLAIM`
- `DEFINITION`
- `CASE`
- `IMPORT`
- `CERTIFICATE`
- `FORMAL_THEOREM`
- `AXIOM`
- `GAP`
- `COUNTEREXAMPLE`

Edge types:

- `because`
- `defines`
- `specializes`
- `uses-hypothesis`
- `discharges`
- `checked-by`
- `imports`
- `contradicts`
- `equivalent-to`

Every theorem-bearing edge names its direction. Association, similarity, and
shared notation are not implication edges. The graph export must retain exact
anchors to proof frames, sources, certificates, and Lean declarations.

The graph validator must reject:

- target-reachable `GAP` nodes when completion is claimed;
- dependency cycles that contain no independently grounded node;
- claims with undeclared variables;
- hypotheses without provenance;
- certificates with no statement bridge;
- imports without exact versions and hypothesis maps;
- status escalation based only on testing or replay;
- a target whose formal declaration is not statement-equivalent to its target
  record.

## 6. Analytic and integral-form polish

Some current subarguments are naturally integral but do not yet have a true,
simplified closed form. Improving them is a proof-development objective because
canonical forms reduce sign ambiguity and formalization cost. It is not a
paper-revision task.

For each such subargument:

1. preserve the original expression and its domain;
2. propose a canonical integral, primitive, determinant, expectation, or
   positive-kernel form;
3. prove equality in both directions, including constants and endpoints;
4. state convergence, measurability, integrability, and differentiation-under-
   the-integral hypotheses;
5. expose all denominator and orientation signs;
6. isolate a manifestly nonnegative integrand when one truly exists;
7. prove the strictness condition separately;
8. compare formal complexity before adopting the new form;
9. retain failed transformations in the audit record.

A shorter formula is not automatically better. The preferred form minimizes
hidden side conditions and makes the downstream implication easiest to check in
Lean. CAS output is discovery support; the equivalence proof remains an
obligation.

## 7. Computational evidence

### 7.1 Exact inputs and conclusions

The theorem-bearing path may consume exact integers, rationals, algebraic
numbers with isolating data, polynomials, symbolic identities, or directed
intervals with justified outward rounding. Floating point is allowed for
discovery, diagnostics, visualization, regression, and counterexample search,
but not as the final decider of a strict sign.

Each computation records:

- its mathematical proposition;
- exact inputs and domains;
- output certificate;
- independent verifier;
- soundness assumptions;
- trusted software boundary;
- downstream theorem uses;
- failure behavior.

### 7.2 Generator/verifier separation

Whenever practical, certificate generation and verification are separate. A
verifier must reconstruct the proposition from canonical inputs rather than
trusting a generator-supplied label, positivity annotation, or simplified
target. Reproducing a stored output or hash establishes reproducibility only.

### 7.3 Permitted certificate patterns

Useful finite witnesses include polynomial identities, rational
factorizations, Bernstein coefficients, Sturm chains, exact determinant
expansions, directed interval enclosures, monotonicity certificates,
tail-majorant parameters, and finite combinatorial derivations. Each requires a
proved bridge from the finite witness to the quantified mathematical claim.

## 8. Lean 4 implementation plan

Lean 4 is the designated proof engine. The formalization proceeds only after a
coherent first pass of the expanded-because graph exists, then advances in
dependency order.

### Phase L0 — foundation and policy

- Pin Lean, Lake, and mathlib versions.
- Record allowed axioms and the trusted base.
- Add build checks forbidding `sorry`, `admit`, `by_contra!`-style placeholders
  used without completed goals, `unsafe` theorem bridges, and unreviewed custom
  axioms.
- Record the output of `#print axioms` for every exported theorem.
- Make the clean build fail on placeholders, missing generated certificates,
  or target-statement drift.

`by_contra`, classical reasoning, and other legitimate proof techniques are
not cheating. Hidden assumptions, placeholders, and unchecked theorem bridges
are. The policy checker must distinguish syntax from logical trust.

### Phase L1 — definitions and target skeleton

- Formalize the target statement before proving it.
- Define the kernel, ordered node configurations, translation minors, strict
  PF order, confluent objects, and all local invariants with explicit domains.
- Prove inhabitation and basic well-definedness lemmas.
- Create named declarations for every proof obligation; none may initially be
  mislabeled complete.

### Phase L2 — generic mathematics

- Formalize determinant normalization, quotient/Wronskian identities,
  divided-difference and iterated-integral lemmas, changes of variables, and
  local-to-global implications for a general kernel.
- Keep kernel-specific estimates out of this layer.
- Prove all orientation, denominator, endpoint, and strictness lemmas.

### Phase L3 — analytic kernel instance

- Formalize or precisely import series convergence, termwise differentiation,
  regularity, parity, positivity, and decay.
- Connect exact certificates for global sign inequalities through verified
  statement bridges.
- Prefer closed integral forms adopted under Section 6.

### Phase L4 — transport and crossing

- Define measures, densities, CDFs, and support intervals.
- Prove normalization and nonempty support before probability notation is used.
- Prove the density-ratio identity and sign from derived premises.
- Prove endpoint limits, unique crossing, derivative sign pattern, and strict
  CDF-gap positivity without assumed-positive stand-ins.
- Derive the transport integral and its strict sign.

### Phase L5 — assembly and obstruction

- Assemble the exact target theorem from the generic and instance layers.
- Formalize the finite order-five obstruction and its relation to confluent or
  distinct nodes.
- Export separate theorems for each promised conclusion.

### Phase L6 — adversarial closure

- Run statement-diff, axiom, placeholder, dependency, and non-vacuity audits.
- Rebuild in a clean environment.
- Attack every strict inequality, endpoint, denominator, limit, ordering case,
  and certificate bridge.
- Claim completion only when the target-reachable graph contains no gaps.

## 9. No-cheating policy

The following are forbidden on a theorem-bearing path:

- `sorry`, `admit`, placeholder tactics, or generated declarations containing
  them;
- undeclared `axiom` or `constant` statements carrying mathematical content;
- treating an `opaque`, `unsafe`, foreign-function, oracle, or runtime result as
  a theorem without a named trusted boundary;
- proving a proposition from `False` without a target-derived proof that the
  relevant case is impossible;
- encoding the desired conclusion in a subtype or typeclass instance and then
  presenting projection as proof;
- assumption laundering through CAS symbol properties, interval constructors,
  theorem parameters, or certificate metadata;
- replacing infinite domains with finite enumerations without a proved
  reduction theorem;
- using numerical tolerance as equality or as a strict-sign decision;
- omitting failed branches, boundary cases, or exceptional denominators;
- importing a stronger hypothesis than the target and forgetting to discharge
  it;
- defining a new object with the desired property and failing to prove it is
  the target object;
- declaring a build successful when the exported theorem has drifted from the
  target contract.

Every exception must be an explicit, versioned trusted-base decision. There are
no silent exceptions.

## 10. Status system

Each claim has exactly one status:

- `UNPARSED` — source claim not yet normalized.
- `OBLIGATION` — exact statement exists; proof is open.
- `CONJECTURE` — proposed but not established.
- `TESTED` — finite or randomized tests passed.
- `SYMBOLICALLY_CHECKED` — a finite symbolic identity was checked.
- `CERTIFIED` — a finite certificate was checked by the named verifier.
- `CONVENTIONALLY_PROVED` — a complete readable derivation is present.
- `IMPORTED` — exact external theorem and hypothesis map are recorded.
- `FORMALLY_PROVED` — Lean's kernel checked the declaration under the recorded
  axioms, without placeholders.
- `REFUTED` — a checked counterexample contradicts the claim.

Statuses describe evidence; they do not form an automatic promotion ladder. A
claim can be conventionally proved yet lack a formal proof, or certified yet
depend on an unformalized bridge.

## 11. Proof-obligation record

Every obligation uses this schema:

```markdown
## PO-XXXX: Short name

Frame:
Stable proof-section or claim anchor.

Statement:
Exact proposition.

Quantifiers and domains:
All variables, types, constraints, and endpoints.

Hypotheses:
Every assumption, with target or prior-obligation provenance.

Conclusion:
Exact result derived.

Non-vacuity witness:
Construction or theorem showing the local context is inhabited and applicable.

Depends on:
Prior obligations, formal theorems, imports, certificates, or axioms.

Expanded because:
Immediate inference edges, one per line.

Method:
Conventional proof, Lean proof, certificate, or import.

Verifier:
Path and exact invocation when applicable.

Trusted base:
Software, axioms, and imported kernels used here.

Counterexample condition:
Concrete condition refuting this statement.

Coverage:
Cases, endpoints, degeneracies, and quantifier ranges checked.

Status:
One status from Section 10.

Notes:
No unstated mathematical reasoning.
```

## 12. Planned document set

The proof system should evolve toward this structure:

```text
proof/
├── SPECIFICATIONS.MD
├── README.md
├── TARGET.md
├── ROADMAP.md
├── STATUS.md
├── TRUSTED_BASE.md
├── DEPENDENCIES.md
├── IMPORTS.md
├── NON_VACUITY.md
├── CLAIM_INDEX.md
├── frames/
│   └── <stable-section-id>.md
├── obligations/
│   └── PO-XXXX.md
├── definitions/
├── analytic/
├── generic/
├── instance/
├── transport/
├── crossing/
├── obstructions/
├── integral_forms/
├── literature/
├── certificates/
├── verifiers/
├── lean/
├── counterexample_search/
└── audit/
```

`counterexample_search/` is falsification work only. Failure to find a
counterexample never proves a universal claim. `audit/` retains attacks, failed
proofs, suspected gaps, theorem drift, and their resolutions. Failed work is
not deleted merely because a later route succeeds.

The documents have distinct roles:

- `TARGET.md` freezes exact theorem versions and non-goals.
- `ROADMAP.md` orders work without claiming proof status.
- `STATUS.md` reports every obligation and blocking edge.
- `TRUSTED_BASE.md` names all trust, including Lean axioms and external
  certificate checkers.
- `DEPENDENCIES.md` is the target-reachable proof graph.
- `IMPORTS.md` is the transitive literature ledger.
- `NON_VACUITY.md` is the global assumption and inhabitation audit.
- `CLAIM_INDEX.md` maps paper claims, proof frames, obligations, certificates,
  and Lean declarations.

Directories should be created when their first real artifact exists; empty
structure is not progress.

## 13. Initial obligation families

The first graph pass should enumerate, without yet claiming completion:

1. target equivalence and statement fidelity;
2. foundational definitions and inhabitation;
3. analytic existence, convergence, regularity, and differentiation;
4. generic determinant, quotient, Wronskian, divided-difference, and
   iterated-integral machinery;
5. kernel-specific global sign inputs;
6. coordinate changes and denominator positivity;
7. measure construction and normalization;
8. non-vacuous one-crossing and CDF-gap theorem;
9. transport identities and strict integral sign;
10. assembly for arbitrary ordered nodes, including lower orders;
11. exact finite obstruction and confluent-to-distinct transfer;
12. transitive imported-mathematics closure;
13. Lean statement, axiom, placeholder, and clean-build audits.

Each family expands into atomic obligations: one mathematical claim per record.

## 14. Adversarial review

Every major theorem receives a separate attack record covering at least:

- inconsistent or uninhabited hypotheses;
- assumptions restated as conclusions;
- object-identity mismatch;
- reversed inequalities and orientation errors;
- empty intervals and missing endpoints;
- zero denominators and invalid logarithms;
- unjustified differentiation, limits, sums, and integrals;
- invalid changes of variable or integration by parts;
- loss of strictness;
- confluent/nonconfluent mismatch;
- hidden compactness or finiteness;
- incomplete ordering cases;
- source-version and theorem-statement drift;
- citation dependency gaps;
- certificate/generator/verifier mismatch;
- formal-target drift and undeclared axioms.

An attack record may refute a claim or reveal a gap. If it finds neither, its
status is only a completed falsification attempt.

## 15. Definition of done

The project may claim proof completion under this specification only when:

1. the versioned target theorem is present in Lean with the same mathematical
   statement;
2. the Lean build succeeds without placeholders;
3. `#print axioms` matches the declared trusted base;
4. every target-reachable graph node terminates in a checked formal theorem,
   a formally connected certificate, or a named foundation;
5. every imported theorem has an exact statement, source, version, transitive
   dependency disposition, and hypothesis map;
6. all quantified domains and local contexts pass the non-vacuity checks;
7. every analytic operation is proved or exactly imported;
8. no theorem-bearing strict sign is decided by floating point;
9. no conclusion is merely an encoded assumption;
10. the crossing/CDF argument is derived from actual measures rather than
    positive symbolic stand-ins;
11. every endpoint, ordering, degenerate, and confluent case admitted by the
    target is covered;
12. an independent clean rebuild checks the exported theorem and certificates;
13. the adversarial audit has no unresolved target-reachable finding.

Before then, status reports must name the strongest checked result and the
unresolved edge. They must not describe the formal proof as complete.

## 16. Guiding principle

The aim is not a performance of certainty. It is an exposed derivation whose
objects exist, whose premises apply, whose quantifiers are covered, whose trust
is named, and whose conclusion cannot admit a counterexample without breaking a
specific checked boundary.
