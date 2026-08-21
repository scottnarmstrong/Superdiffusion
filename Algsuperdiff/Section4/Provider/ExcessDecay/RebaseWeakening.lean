/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepConsumerLegBudget
import Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

/-! ## 1. The scalar move -/

/-- **The two leg moves, as one scalar inequality.**

`rpow_neg_nine_halves_le_rpow_neg_six` is exactly this fact; it is re-exported
here under a re-base name so that the harmonic lane reads it from its own module
rather than through the excess-decay consumer check. -/
theorem rpow_legMove_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow s (-(9 / 2 : ℝ)) ≤ Real.rpow s (-(6 : ℝ)) :=
  rpow_neg_nine_halves_le_rpow_neg_six hs hs1

/-! ## 2. The real-valued leg -/

/-- One leg of a real-valued clause, moved.  The leg's shape is the one every
proved transcription uses: the `s`-power, then a nonnegative `3`-power, then
the `toReal` of an `ℝ≥0∞` seminorm. -/
theorem rpow_legMove_mul_le {s a T : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 ≤ a)
    (hT : 0 ≤ T) :
    Real.rpow s (-(9 / 2 : ℝ)) * a * T ≤ Real.rpow s (-(6 : ℝ)) * a * T := by
  have hmove := rpow_legMove_le hs hs1
  have hstep : Real.rpow s (-(9 / 2 : ℝ)) * a ≤ Real.rpow s (-(6 : ℝ)) * a :=
    mul_le_mul_of_nonneg_right hmove ha
  exact mul_le_mul_of_nonneg_right hstep hT

/-- **The real-valued display, with both `∇h` legs moved to `s^{-6}`.**

`H` carries the two untouched summands (the flux bracket and the `σ̄` force leg);
the two `∇h` legs move.  Abstract in every carrier, so this one lemma re-cuts
each `…Real` clause of the lane. -/
theorem realBracket_legMove_le {C s a₄ a₅ T₄ T₅ H : ℝ} (hC : 0 ≤ C)
    (hs : 0 < s) (hs1 : s ≤ 1) (h₄ : 0 ≤ a₄) (h₅ : 0 ≤ a₅) (hT₄ : 0 ≤ T₄)
    (hT₅ : 0 ≤ T₅) :
    C * (H + Real.rpow s (-(9 / 2 : ℝ)) * a₄ * T₄ +
        Real.rpow s (-(9 / 2 : ℝ)) * a₅ * T₅) ≤
      C * (H + Real.rpow s (-(6 : ℝ)) * a₄ * T₄ +
        Real.rpow s (-(6 : ℝ)) * a₅ * T₅) := by
  have e₄ := rpow_legMove_mul_le hs hs1 h₄ hT₄
  have e₅ := rpow_legMove_mul_le hs hs1 h₅ hT₅
  refine mul_le_mul_of_nonneg_left ?_ hC
  linarith only [e₄, e₅]

/-! ## 3. The `ℝ≥0∞` prefactor product -/

/-- **One frozen leg, moved.**  The frozen display's legs 4 and 5 are
`ENNReal.ofReal (C · s^{-9/2} · a) · T` with `a` a `3`-power and `T` an `ℝ≥0∞`
seminorm; the move
raises the prefactor, and `ℝ≥0∞` multiplication is monotone in it with no
finiteness side condition. -/
theorem ofReal_legMove_mul_le {C s a : ℝ} {T : ℝ≥0∞} (hC : 0 ≤ C) (hs : 0 < s)
    (hs1 : s ≤ 1) (ha : 0 ≤ a) :
    ENNReal.ofReal (C * Real.rpow s (-(9 / 2 : ℝ)) * a) * T ≤
      ENNReal.ofReal (C * Real.rpow s (-(6 : ℝ)) * a) * T := by
  have hmove := rpow_legMove_le hs hs1
  have hstep : C * Real.rpow s (-(9 / 2 : ℝ)) * a ≤ C * Real.rpow s (-(6 : ℝ)) * a :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmove hC) ha
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hstep) T

/-- **The frozen `ℝ≥0∞` display, with both `∇h` legs moved to `s^{-6}`.**

`H` carries the first two summands of the frozen general clause (the flux
bracket with its in-bracket `∇h` companion, and the `σ̄` force leg); the two
`∇h` legs move.  This is the shape of the frozen block's own conclusion, so the
lemma applies to it verbatim. -/
theorem ennrealDisplay_legMove_le {C s a₄ a₅ : ℝ} {H T₄ T₅ : ℝ≥0∞}
    (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s ≤ 1) (h₄ : 0 ≤ a₄) (h₅ : 0 ≤ a₅) :
    H + ENNReal.ofReal (C * Real.rpow s (-(9 / 2 : ℝ)) * a₄) * T₄ +
        ENNReal.ofReal (C * Real.rpow s (-(9 / 2 : ℝ)) * a₅) * T₅ ≤
      H + ENNReal.ofReal (C * Real.rpow s (-(6 : ℝ)) * a₄) * T₄ +
        ENNReal.ofReal (C * Real.rpow s (-(6 : ℝ)) * a₅) * T₅ :=
  add_le_add (add_le_add (le_refl H) (ofReal_legMove_mul_le hC hs hs1 h₄))
    (ofReal_legMove_mul_le hC hs hs1 h₅)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
