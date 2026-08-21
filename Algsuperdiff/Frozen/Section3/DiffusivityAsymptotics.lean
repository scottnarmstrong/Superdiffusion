import Algsuperdiff.Frozen.Section3.InductionState
import Algsuperdiff.Section3.Scales
import Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripRemainder

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.diffusivity_asymptotics
    (d : ℕ) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        mStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ m : ℤ, m ≤ m0 →
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) ∧
        (1 / 4 : ℝ) *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
          ≤ (Annealed.sigmaBar M m0 : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M m0 : ℝ) ^ 2
          ≤ 4 *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
-- FROZEN-STATEMENT-END
    := by
  by_cases hd : 2 ≤ d
  · haveI : NeZero d := ⟨by omega⟩
    -- The provider export is gated at `mStarStar`; the frozen gate
    -- `mStar M < m0` is the stronger one, so the composition is a fortiori.
    obtain ⟨Cflow, hCflow, hmain⟩ :=
      Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.diffusivity_asymptotics_proved
        d hd
    exact ⟨Cflow, hCflow, fun M m0 E hm0 =>
      hmain M m0 E (lt_of_le_of_lt (Provider.Scales.mStarStar_le_mStar M) hm0)⟩
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd⟩
