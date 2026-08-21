/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepTriangle
import Algsuperdiff.Section4.Provider.Regularity.StepFourFinalInterior
import Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Item (f): the `toNat` cast bridge, named -/

/-- **The `toNat` cast bridge.**  For `n ≤ m`, the real cast of the natural window
length is the real difference. -/
theorem toNat_sub_cast_real {m n : ℤ} (h : n ≤ m) :
    (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
  have h0 : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  exact_mod_cast congrArg (fun w : ℤ => (w : ℝ)) h0

/-! ## 2. Item (c): the funding-line threshold -/

/-- **The funding-line threshold** `δ₀(d, C, C_ann, k)`.

The Step-6 producer's gate `P·(C_ann·(s/8)√δ) ≤ ½·3^{-k/4}` is linear in `√δ`
at `P = edFinalEpsCoeff d C k s`, so it holds exactly for `δ ≤ (½·3^{-k/4} /
(P·C_ann·(s/8)))²`. -/
def edFundingDelta0 (d : ℕ) [NeZero d] (C Cann : ℝ) (k : ℕ) : ℝ :=
  ((1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) /
      (edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth)) ^ (2 : ℕ)

/-- The `C₁`-floor form of the funding threshold. -/
def edFundingC1Delta0 (d : ℕ) [NeZero d] (C Cann : ℝ) (k : ℕ) : ℝ :=
  (edFundingDelta0 d C Cann k)⁻¹

theorem edFundingDelta0_nonneg (d : ℕ) [NeZero d] (C Cann : ℝ) (k : ℕ) :
    0 ≤ edFundingDelta0 d C Cann k := by
  rw [edFundingDelta0]
  exact sq_nonneg _

/-- **Item (c), proved: the funding line from a `δ`-threshold.** -/
theorem edFunding_of_delta_le (d : ℕ) [NeZero d] {C Cann delta : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hCann : 0 ≤ Cann)
    (hdelta : delta ≤ edFundingDelta0 d C Cann k) :
    edFinalEpsCoeff d C k stepOneS * (Cann * stepOneEp delta) ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) := by
  have hs8 : (0 : ℝ) < stepOneSEighth := stepOneSEighth_pos
  have hP : (0 : ℝ) ≤ edFinalEpsCoeff d C k stepOneS :=
    edFinalEpsCoeff_nonneg d hC k (by rw [stepOneS]; norm_num)
  set A : ℝ := edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth with hAdef
  have hAnn : (0 : ℝ) ≤ A := by
    rw [hAdef]
    exact mul_nonneg (mul_nonneg hP hCann) hs8.le
  set R : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) with hRdef
  have hRpos : (0 : ℝ) < R := by
    rw [hRdef]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith only [h3]
  have hLHS : edFinalEpsCoeff d C k stepOneS * (Cann * stepOneEp delta) =
      A * Real.sqrt delta := by
    rw [hAdef, stepOneEp]; ring
  rw [hLHS]
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · rw [← hA0, zero_mul]
    exact hRpos.le
  · have hratio : (0 : ℝ) < R / A := div_pos hRpos hApos
    have hsq : delta ≤ (R / A) ^ (2 : ℕ) := by
      refine le_trans hdelta (le_of_eq ?_)
      rw [edFundingDelta0, hAdef, hRdef]
    have hsqrt : Real.sqrt delta ≤ R / A := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hratio.le] at h
    have hstep : A * Real.sqrt delta ≤ A * (R / A) :=
      mul_le_mul_of_nonneg_left hsqrt hAnn
    rwa [mul_div_cancel₀ R (ne_of_gt hApos)] at hstep

/-- **Item (c) in the `C₁`-floor shape** (`RootAssemblyParameters` §3's pattern): a
caller carrying `edFunding ≤ C₁` and `0 < α` gets `δ = C₁⁻¹(1-α) ≤ δ₀` for
free. -/
theorem stepOneDelta_le_edFundingDelta0 (d : ℕ) [NeZero d] {C Cann C1 alpha : ℝ}
    {k : ℕ} (hpos : 0 < edFundingDelta0 d C Cann k) (halpha0 : 0 < alpha)
    (hC1 : edFundingC1Delta0 d C Cann k ≤ C1) :
    stepOneDelta C1 alpha ≤ edFundingDelta0 d C Cann k := by
  have hinv0 : (0 : ℝ) < (edFundingDelta0 d C Cann k)⁻¹ := inv_pos.mpr hpos
  have hC1pos : (0 : ℝ) < C1 :=
    lt_of_lt_of_le hinv0 (by rwa [edFundingC1Delta0] at hC1)
  have hmul : (1 : ℝ) ≤ edFundingDelta0 d C Cann k * C1 := by
    calc (1 : ℝ) = edFundingDelta0 d C Cann k * (edFundingDelta0 d C Cann k)⁻¹ :=
          (mul_inv_cancel₀ (ne_of_gt hpos)).symm
      _ ≤ edFundingDelta0 d C Cann k * C1 := by
          refine mul_le_mul_of_nonneg_left ?_ hpos.le
          rwa [edFundingC1Delta0] at hC1
  have hstep : C1⁻¹ ≤ edFundingDelta0 d C Cann k := by
    have h := mul_le_mul_of_nonneg_right hmul (le_of_lt (inv_pos.mpr hC1pos))
    rwa [one_mul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hC1pos), mul_one] at h
  calc stepOneDelta C1 alpha = C1⁻¹ * (1 - alpha) := rfl
    _ ≤ C1⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith only [halpha0])
          (le_of_lt (inv_pos.mpr hC1pos))
    _ = C1⁻¹ := mul_one _
    _ ≤ edFundingDelta0 d C Cann k := hstep

/-! ## 3. Item (d): the affine-minimizer family on the Step-3 windows -/

/-- **Item (d), proved: the affine-minimizer family exists.**

Every Step-4/6 producer binds a pair `(c, slope) : (ℤ → ℝ) × (ℤ → Vec d)`
minimizing the affine distance on `stepThreeWindow z m j` for all `j ≤ m`.  The
family is built scale by scale from the proved
`ExcessDecay.exists_isAffineMinimizer_truncatedWindow` — `stepThreeWindow` IS
`truncatedWindow` by definition — with the `H¹` datum's own `L²` membership
restricted to the window. -/
theorem exists_stepThreeWindow_affineMinimizerFamily {m : ℤ} {z : Vec d}
    (hzm : z ∈ openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) :
    ∃ (c : ℤ → ℝ) (slope : ℤ → Vec d),
      ∀ j : ℤ, j ≤ m →
        Support.IsAffineMinimizer (stepThreeWindow z m j) u.toFun (c j) (slope j) := by
  classical
  have hex : ∀ j : ℤ, ∃ p : ℝ × Vec d,
      j ≤ m →
        Support.IsAffineMinimizer (stepThreeWindow z m j) u.toFun p.1 p.2 := by
    intro j
    by_cases hj : j ≤ m
    · obtain ⟨cj, gj, hcg⟩ :=
        exists_isAffineMinimizer_truncatedWindow (m := m) (k := j) hzm (by omega)
          (u := u.toFun)
          (u.memL2.mono_measure
            (Measure.restrict_mono (truncatedWindow_subset_domain z m j) le_rfl))
      exact ⟨(cj, gj), fun _ => hcg⟩
    · exact ⟨(0, 0), fun hcontra => absurd hcontra hj⟩
  exact ⟨fun j => (hex j).choose.1, fun j => (hex j).choose.2,
    fun j hj => (hex j).choose_spec hj⟩

end

end Algsuperdiff.Section4.Provider.Regularity
