"""Mechanically extract the concrete theta-tail layer from the audited round.

The analytic and generic infinite-sum lemmas are imported from their maintained
modules.  This generator preserves the concrete definitions and proofs while
removing the obsolete duplicated foundations.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "work/2026-07-21-infinite-tail-theorem-refactor/RelativeTailRefactor.lean"
TARGET = Path(__file__).with_name("CERT12ThetaTail.scaffold.lean")

source = SOURCE.read_text()

definitions_start = source.index("noncomputable def firstModeScale")
definitions_end = source.index("/-- Every polynomial occurring")
definitions = source[definitions_start:definitions_end]

concrete_start = source.index("theorem modeX_ge_27")
generic_start = source.index("/-- A pointwise geometric majorant")
concrete_prefix = source[concrete_start:generic_start]

composition_start = source.index("/-- The intended concrete interface")
composition_end = source.index("/-- Same-sign summands")
composition = source[composition_start:composition_end]

body = definitions + concrete_prefix + composition
body = body.replace("apply lt_of_le_of_lt (le_norm δ)",
                    "apply lt_of_le_of_lt (Real.le_norm_self δ)")

header = """/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12GeometricTsum
import PF4.ClearedJetCertificateBridge
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal normalized theta-tail control for CERT12

This module connects the maintained half-line and geometric-series bounds to
the literal `PF4.thetaSeriesJet`.  Its exported theorem removes the infinite
tail from the theorem-facing boundary without a finite cutoff.
-/

namespace PF4.CERT12ThetaTail

open Finset Set
open PF4.CERT12TailPolynomial
open PF4.CERT12TailExponential
open PF4.CERT12GeometricTsum

"""

footer = """
end PF4.CERT12ThetaTail

#print axioms PF4.CERT12ThetaTail.laterModeTail_lt_one_thousandth_closed
#print axioms PF4.CERT12ThetaTail.fullModeTail_eq_third_mul_one_add_relative_closed
#print axioms PF4.CERT12ThetaTail.normalizedSeriesJet_eq_first_three_relative
"""

TARGET.write_text(header + body + footer)
