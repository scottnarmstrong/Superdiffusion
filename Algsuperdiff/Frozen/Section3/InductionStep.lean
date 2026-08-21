import Algsuperdiff.Frozen.Section3.InductionState
import Algsuperdiff.Section3.Provider.Induction.InductionStepAssembly

open Algsuperdiff.Section3
open Homogenization MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.induction_step
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        Algsuperdiff.Frozen.Section3.inductionState M m E
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section3.Provider.Induction.induction_step_provided d
