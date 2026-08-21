import Algsuperdiff.Frozen.Section3.InductionState
import Algsuperdiff.Section3.Probability.OneSidedOrlicz
import Algsuperdiff.Frozen.Section3.CoarseEllipticityBounds
import Algsuperdiff.Section3.Provider.Tail.TailAssembly

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.tail_bounds
    (d : ℕ) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (4 * M.gamma) 1,
          max Ctail (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          Probability.IsDeterministicShiftTwoTermOneSidedOrlicz
            (Cutoff.cutoffSampleLaw M).toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            (Homogenization.IndependentSums.gammaSigma (1 / 2))
            (Observable.cutoffHomogenizationErrorAtComparatorScale
              M m (m - 1)
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 4)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
            Ctail
            (Ctail * (Real.sqrt (Disorder.cstar M))⁻¹ *
              s⁻¹ * Real.sqrt M.gamma)
            (Real.exp
              (-(Ctail⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Tail.tail_bounds_of_coarse_ellipticity_bounds d
    (Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d)
