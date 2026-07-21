# Failure ledger

1. The first factor-identity proof placed `ring` after `field_simp`, but
   `field_simp` had already normalized and closed the goal. Lean correctly
   rejected the redundant tactic with `No goals to be solved`. Removing the
   extra line repaired the tactic script; the mathematical identity did not
   change.
