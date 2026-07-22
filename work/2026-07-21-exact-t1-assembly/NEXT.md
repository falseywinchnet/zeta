# Next round

Run a refine round to integrate `ExactT1Assembly.lean` as the maintained exact
T1 theorem.

1. Choose the narrow maintained module boundary and public theorem name.
2. Preserve the real-valued lower-order determinant factorizations and quotient
   sign dependencies.
3. Import the module from the maintained root, add `#print axioms` coverage, and
   create a replayable certificate.
4. Run the complete maintained build and audit.
5. Update `proof/TARGET.md`, `proof/NEXT_ADVANCEMENT.md`, and the programme
   ledger to distinguish closed T1 from the still-open PF5 and downstream
   zero-counterexample targets.

Do not weaken the theorem to a grid, compact node set, or non-strict minor
statement during integration.
