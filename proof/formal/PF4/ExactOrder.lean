/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.GlobalStrictPF4
import PF4.PF5Witness

set_option linter.style.header false

/-!
# Exact Pólya-frequency order of the global Riemann kernel

This module performs only the target-level T3 assembly.  T1 supplies
nonnegative minors through order four.  If PF5 held, its universal
quantifiers could be instantiated at the exact ordered CERT17 witness nodes,
contradicting T2's strictly negative determinant.
-/

namespace PF4

/-- T3: the maintained global Riemann kernel has exact finite PF order four. -/
theorem globalRiemannKernel_pfOrderExactly_four :
    PFOrderExactly globalRiemannKernel 4 := by
  constructor
  · exact globalRiemannKernel_strictPFUpTo_four.pfUpTo
  · intro hpf5
    have hnodes :
        StrictMono (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ)) := by
      change StrictMono pf5WitnessNodes
      exact pf5WitnessNodes_strictMono
    have hnonneg :
        0 ≤ translationMinor globalRiemannKernel
          (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ))
          (fun j : Fin 5 => ((j : ℕ) : ℝ) * (211 / 2000 : ℝ)) :=
      hpf5 5 (by norm_num) (by norm_num) _ _ hnodes hnodes
    exact (not_lt_of_ge hnonneg)
      globalRiemannKernel_orderFive_translationMinor_neg

end PF4
