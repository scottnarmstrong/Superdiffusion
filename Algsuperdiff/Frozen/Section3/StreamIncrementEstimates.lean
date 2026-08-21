import Algsuperdiff.Section3.Provider.Stream.IncrementEstimates

open Algsuperdiff.Section3

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.stream_increment_estimates
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (M : ABKModel d) (p : ℝ), 1 ≤ p →
        ∀ l m n : ℤ, n < m → m ≤ l →
          Homogenization.Book.Ch04.IsBigO
            M.P.toMeasure
            (Homogenization.Book.Ch04.gammaSigma 1)
            (fun omega : Cutoff.ShellSeq d =>
              Provider.Stream.cubeFrobeniusMassFiniteShellIncrement l n m omega -
                (Disorder.cstarPlus M * Real.log 3) *
                  ∑ k ∈ Finset.Ioc n m,
                    (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))
            (C * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) ∧
          Probability.IsDeterministicShiftOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1)
            (fun omega => Provider.Stream.streamIncrementLpNorm p l n m omega ^ 2)
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))))
            (C * p *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / p) * ((l : ℝ) - (m : ℝ)))) ∧
          Probability.IsOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1)
            (fun omega : Cutoff.ShellSeq d =>
              Provider.Stream.streamIncrementLinftyNorm n n m omega ^ 2)
            (C * min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ∧
          Probability.IsOneSidedOrlicz
            M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 1)
            (fun omega : Cutoff.ShellSeq d =>
              Provider.Stream.streamIncrementLinftyNorm l n m omega ^ 2)
            (C * ((l : ℝ) - (n : ℝ)) *
              min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) ∧
      ∀ (M : ABKModel d) (l m n : ℤ), n ≤ min m l →
        Homogenization.IndependentSums.IsBigOWith
          M.P.toMeasure
          (Homogenization.IndependentSums.gammaSigma 2)
          (fun omega : Cutoff.ShellSeq d =>
            ∑ k ∈ Finset.Ioc n m,
              ((3 : ℝ) ^ k * Provider.Stream.localCubeDerivNorm l (omega k) +
                (3 : ℝ) ^ (2 * k) *
                  Provider.Stream.localCubeSecondDerivNorm l (omega k)))
          (C * Real.sqrt (max 1 ((l : ℝ) - (n : ℝ))) *
            min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Stream.stream_increment_estimates_provider d
