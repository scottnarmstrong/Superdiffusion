import Algsuperdiff.Frozen.Section3.InductionState
import Algsuperdiff.Section3.Probability.TwoTermOrlicz
import Algsuperdiff.Section3.Observable.CutoffHomogenizationError
import Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleComposition

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.multiscale_estimate
    (d : ℕ) :
    ∃ Cms : ℝ, 0 < Cms ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            ∃ Y Z : Cutoff.CutoffSample d → ℝ,
              Probability.IsTwoTermBigOWithWitnesses
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (Homogenization.IndependentSums.gammaSigma 2)
                  (Homogenization.IndependentSums.gammaSigma (1 / 2))
                  (Observable.cutoffHomogenizationError M m
                    ⟨s,
                      (mul_pos (by norm_num : (0 : ℝ) < 8)
                        M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
                  Y Z
                  (Cms * (E : ℝ) * s⁻¹ *
                    Real.sqrt (epsilon * M.gamma))
                  (Cms * epsilon * (s⁻¹) ^ 2 *
                    Real.exp
                      (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
                (s ≤ Cms * epsilon →
                  Homogenization.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2)
                    Y
                    (Cms * epsilon * (E : ℝ) * s⁻¹ *
                      Real.sqrt M.gamma))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.MultiscaleEstimate.multiscale_estimate_composed d
