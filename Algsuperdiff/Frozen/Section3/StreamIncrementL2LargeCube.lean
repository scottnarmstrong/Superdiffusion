import Algsuperdiff.Section3.Provider.Stream.IncrementL2LargeCube

open Algsuperdiff.Section3

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.stream_increment_l2_large_cube_bound
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (l m n : ℤ), n < m → m ≤ l →
        Homogenization.Book.Ch04.IsBigO
          M.P.toMeasure
          (Homogenization.Book.Ch04.gammaSigma 1)
          (fun omega : Cutoff.ShellSeq d =>
            Provider.Stream.cubeFrobeniusMassFiniteShellIncrement l n m omega -
              (Disorder.cstarPlus M * Real.log 3) *
                ∑ k ∈ Finset.Ioc n m,
                  (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))
          (C * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Stream.stream_increment_l2_large_cube_bound_provider d
