import Algsuperdiff.Section3.Provider.Stream.IncrementLpNormSqAllP

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.stream_increment_lp_norm_sq_large_cube_bound
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (p : ℝ), 1 ≤ p →
        ∀ l m n : ℤ, n < m → m ≤ l →
          Probability.IsDeterministicShiftOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1)
            (fun omega ↦ Provider.Stream.streamIncrementLpNorm p l n m omega ^ 2)
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))))
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ))))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Stream.stream_increment_lp_norm_sq_large_cube_bound_provider d
