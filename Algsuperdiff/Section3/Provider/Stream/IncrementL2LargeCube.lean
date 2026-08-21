import Algsuperdiff.Section3.Provider.Stream.LayerL2Bound

/-!
# Squared L2 stream-increment estimate

This module packages the corrected all-gap centered Frobenius estimate with a
single positive dimension-only amplitude.  The endpoint is an ordinary
provider for the separately approved source-facing declaration.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Dimension-only provider for the corrected squared normalized `L2`
stream-increment estimate. -/
theorem stream_increment_l2_large_cube_bound_provider (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (l m n : ℤ), n < m → m ≤ l →
        Homogenization.Book.Ch04.IsBigO
          M.P.toMeasure
          (Homogenization.Book.Ch04.gammaSigma 1)
          (fun omega : ShellSeq d =>
            cubeFrobeniusMassFiniteShellIncrement l n m omega -
              (Disorder.cstarPlus M * Real.log 3) *
                ∑ k ∈ Finset.Ioc n m,
                  (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))
          (C * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := by
  let C : ℝ := max 1 (layerL2AllGapConst d)
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (layerL2AllGapConst d))
  refine ⟨C, hCpos, ?_⟩
  intro M l m n hnm _hml
  have h := cubeFrobeniusMassFiniteShellIncrement_centered_isBigO_allGap
    M (l := l) hnm
  have hconst : layerL2AllGapConst d ≤ C := by
    exact le_max_right 1 (layerL2AllGapConst d)
  have hscale :
      layerL2AllGapConst d *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) ≤
        C * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  have h' := h.mono_scale hscale
  simpa only [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h'

end

end Algsuperdiff.Section3.Provider.Stream
