import Algsuperdiff.Section3.Provider.Stream.StreamDerivativeSum

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.stream_derivative_sum_bound
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (l m n : ℤ), n ≤ min m l →
        Homogenization.IndependentSums.IsBigOWith
          M.P.toMeasure
          (Homogenization.IndependentSums.gammaSigma 2)
          (fun omega : Cutoff.ShellSeq d =>
            ∑ k ∈ Finset.Ioc n m,
              ((3 : ℝ) ^ k *
                  Provider.Stream.localCubeDerivNorm l (omega k) +
                (3 : ℝ) ^ (2 * k) *
                  Provider.Stream.localCubeSecondDerivNorm l (omega k)))
          (C * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Stream.stream_derivative_sum_bound_provider d
