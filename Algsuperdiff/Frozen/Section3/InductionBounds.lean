import Algsuperdiff.Frozen.Section3.InductionState
import Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
import Algsuperdiff.Section3.Observable.CutoffHomogenizationError
import Algsuperdiff.Section3.Provider.Induction.InductionBoundsAssembly

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.induction_bounds
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        (∀ m : ℤ,
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (Homogenization.IndependentSums.gammaSigma 2)
              (Homogenization.IndependentSums.gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M m
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              (C * (Disorder.cstar M)⁻¹ * s⁻¹ *
                Real.sqrt M.gamma)
              (Real.exp
                (-(C⁻¹ * (Disorder.cstar M) ^ 3 *
                  M.gamma⁻¹)))) ∧
        (∀ m : ℤ,
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ C * (Disorder.cstar M)⁻¹ ^ 2 *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Induction.induction_bounds_provided d
