import Algsuperdiff.Frozen.Section3.InductionState
import Algsuperdiff.Section3.Scales
import Algsuperdiff.Section3.Probability.OneSidedOrlicz
import Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
import Algsuperdiff.Section3.Observable.CutoffHomogenizationError
import Algsuperdiff.Section3.Provider.Base.BaseCaseAssembly

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.base_case
    (d : ℕ) :
    ∃ C0 Cstart : ℝ, 0 < C0 ∧ 0 < Cstart ∧
      ∀ M : ABKModel d,
        (∀ m : ℤ,
          M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
          (Annealed.sigmaBar M m : ℝ) ≤
            M.nu *
              (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ *
                M.gamma⁻¹ * (1 + 4 * M.gamma) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ∧
          ∀ s : {s : ℝ // s ∈ Set.Ioo 0 1},
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (Homogenization.IndependentSums.gammaSigma 2)
              (Homogenization.IndependentSums.gammaSigma 4)
              (Observable.cutoffHomogenizationError M m
                ⟨(s : ℝ), s.property.1⟩)
              (C0 * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
                (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
                  Real.sqrt (baseLoss d s))
              (C0 * (Real.sqrt M.nu)⁻¹ *
                (Real.sqrt (Real.sqrt M.gamma))⁻¹ *
                  (3 : ℝ) ^ (M.gamma * (m : ℝ) / 2) *
                    Real.sqrt (Real.sqrt (baseLoss d s)))) ∧
        (∀ m : ℤ, m ≤ mStarStar M →
          M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
          (Annealed.sigmaBar M m : ℝ) ≤ (1 + M.gamma ^ 2) * M.nu ∧
          ∀ s : {s : ℝ // s ∈ Set.Ioo 0 1},
            Probability.IsOneSidedOrlicz
              (Cutoff.cutoffSampleLaw M).toMeasure
              (Homogenization.IndependentSums.gammaSigma 2)
              (Observable.cutoffHomogenizationError M m
                ⟨(s : ℝ), s.property.1⟩)
              (C0 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
                Real.sqrt M.gamma * Real.sqrt (baseLoss d s))) ∧
        (∀ m : ℤ, m ≤ mStar M →
          M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
          (Annealed.sigmaBar M m : ℝ) ≤ 2 * M.nu ∧
          ∀ s : {s : ℝ // s ∈ Set.Ioo 0 1},
            Probability.IsDeterministicShiftOneSidedOrlicz
              (Cutoff.cutoffSampleLaw M).toMeasure
              (Homogenization.IndependentSums.gammaSigma 2)
              (Observable.cutoffHomogenizationError M m
                ⟨(s : ℝ), s.property.1⟩)
              2
              (C0 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
                Real.sqrt (baseLoss d s))) ∧
        ∃ Estart : {E : ℝ // 1 ≤ E},
          (Estart : ℝ) = Cstart * (Real.sqrt (Disorder.cstar M))⁻¹ ∧
          Algsuperdiff.Frozen.Section3.inductionState
            M (mStarStar M) Estart
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Base.base_case d
