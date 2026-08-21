import Algsuperdiff.Section3.Probability.OneSidedOrlicz
import Algsuperdiff.Section3.Provider.Stream.IncrementLp
import Algsuperdiff.Section3.Provider.Stream.MomentBoostedLargeAllP

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.stream_increment_lp_large_cube_bound
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (p : ℝ), 1 ≤ p →
        ∀ l m n : ℤ, n < m → m ≤ l →
          Probability.IsDeterministicShiftOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma (2 / p))
            (Provider.Stream.streamIncrementLpMass p l n m)
            ((C * p) ^ (p / 2) *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2))
            ((C * p) ^ (p / 2) *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Stream.stream_increment_lp_large_cube_bound_provider d
