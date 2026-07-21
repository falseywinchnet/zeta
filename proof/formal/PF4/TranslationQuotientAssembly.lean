import PF4.QuotientIntegral
import PF4.TranslationQuotientTower

set_option linter.style.header false

/-!
# Translation quotient tower: determinant assembly

This leaf module is the only connection from the actual translation quotient
tower to the iterated-integral determinant engine. Keeping it separate prevents
changes to the 646-line integral engine from invalidating the lower quotient
objects and sign conversions.
-/

namespace PF4.TranslationQuotientTower

open PF4.ContinuousQuotientBox

theorem translate_mul_firstQuot {Φ : ℝ → ℝ} (hΦpos : ∀ t, 0 < Φ t)
    (a b r : ℝ) :
    Φ (r - a) * firstQuot Φ a b r = Φ (r - b) := by
  unfold firstQuot
  field_simp [(hΦpos (r - a)).ne']

theorem translationMinor_eq_rawFactoredDet4 {Φ : ℝ → ℝ}
    (hΦpos : ∀ t, 0 < Φ t) (t₁ t₂ t₃ t₄ y₁ y₂ y₃ y₄ : ℝ) :
    PF4.translationMinor Φ ![t₁, t₂, t₃, t₄] ![y₁, y₂, y₃, y₄] =
      rawFactoredDet4
        (Φ (t₁ - y₁)) (Φ (t₂ - y₁)) (Φ (t₃ - y₁)) (Φ (t₄ - y₁))
        (firstQuot Φ y₁ y₂ t₁) (firstQuot Φ y₁ y₃ t₁) (firstQuot Φ y₁ y₄ t₁)
        (firstQuot Φ y₁ y₂ t₂) (firstQuot Φ y₁ y₃ t₂) (firstQuot Φ y₁ y₄ t₂)
        (firstQuot Φ y₁ y₂ t₃) (firstQuot Φ y₁ y₃ t₃) (firstQuot Φ y₁ y₄ t₃)
        (firstQuot Φ y₁ y₂ t₄) (firstQuot Φ y₁ y₃ t₄)
        (firstQuot Φ y₁ y₄ t₄) := by
  unfold PF4.translationMinor PF4.translationMatrix rawFactoredDet4
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translate_mul_firstQuot hΦpos]

/-- Conditional instantiation boundary: for the actual translate quotient
tower, strict positivity of the three quotient levels (`v₂ = A' > 0`,
`w₃ = V' > 0`, `q' > 0`) forces strict positivity of the original order-four
translation minor at strictly increasing rows. The three level signs are the
named upstream conversion boundary; no minor, Wronskian, finite difference,
integral, or terminal quotient-derivative sign is assumed elsewhere. -/
theorem translationMinor_pos_of_quotient_tower_signs
    {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {t₁ t₂ t₃ t₄ y₁ y₂ y₃ y₄ : ℝ}
    (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃) (ht₃₄ : t₃ < t₄)
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦ2 : ∀ t, HasDerivAt Φ2 (Φ3 t) t)
    (hΦ3c : Continuous Φ3)
    (hΦpos : ∀ t, 0 < Φ t)
    (hfirst : ∀ t, 0 < firstQuotD Φ Φ1 y₁ y₂ t)
    (hsecond : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t)
    (hterminal : ∀ t, 0 < terminalQuotD Φ Φ1 Φ2 Φ3 y₁ y₂ y₃ y₄ t) :
    0 < PF4.translationMinor Φ ![t₁, t₂, t₃, t₄] ![y₁, y₂, y₃, y₄] := by
  have hΦc : Continuous Φ :=
    continuous_iff_continuousAt.mpr fun t => (hΦ t).continuousAt
  have hΦ1c : Continuous Φ1 :=
    continuous_iff_continuousAt.mpr fun t => (hΦ1 t).continuousAt
  have hΦ2c : Continuous Φ2 :=
    continuous_iff_continuousAt.mpr fun t => (hΦ2 t).continuousAt
  rw [translationMinor_eq_rawFactoredDet4 hΦpos t₁ t₂ t₃ t₄ y₁ y₂ y₃ y₄]
  exact rawFactoredDet4_pos_of_full_quotient_chain ht₁₂ ht₂₃ ht₃₄
    (hΦpos (t₁ - y₁)) (hΦpos (t₂ - y₁)) (hΦpos (t₃ - y₁)) (hΦpos (t₄ - y₁))
    (fun t => hasDerivAt_firstQuot hΦ hΦpos y₁ y₂ t)
    (fun t => hasDerivAt_firstQuot hΦ hΦpos y₁ y₃ t)
    (fun t => hasDerivAt_firstQuot hΦ hΦpos y₁ y₄ t)
    (fun t => hasDerivAt_secondQuot hΦ hΦ1 hΦpos hfirst y₃ t)
    (fun t => hasDerivAt_secondQuot hΦ hΦ1 hΦpos hfirst y₄ t)
    (fun t => hasDerivAt_terminalQuot hΦ hΦ1 hΦ2 hΦpos hfirst hsecond y₄ t)
    (continuous_firstQuotD hΦc hΦ1c hΦpos y₁ y₂)
    (continuous_firstQuotD hΦc hΦ1c hΦpos y₁ y₃)
    (continuous_firstQuotD hΦc hΦ1c hΦpos y₁ y₄)
    (continuous_secondQuotD hΦc hΦ1c hΦ2c hΦpos hfirst y₃)
    (continuous_secondQuotD hΦc hΦ1c hΦ2c hΦpos hfirst y₄)
    (continuous_terminalQuotD hΦc hΦ1c hΦ2c hΦ3c hΦpos hfirst hsecond y₄)
    (fun t => firstQuotD_factor hfirst y₃ t)
    (fun t => firstQuotD_factor hfirst y₄ t)
    (fun t => secondQuotD_factor hsecond y₄ t)
    hfirst hsecond hterminal

end PF4.TranslationQuotientTower
