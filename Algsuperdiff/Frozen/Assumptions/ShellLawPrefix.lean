import Algsuperdiff.Assumptions.ShellField.SequenceLaw
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
/-- The `nu`-free shell-law prefix from ABK26:
the paper-wide dimension and scaling parameters, mutual independence of all
shells, and the exact marginal scaling law under the canonical sequence law.
Molecular diffusivity `nu > 0` is deferred to the
cutoff/coefficient parameter surface.  Antisymmetry and the author-approved
qualitative `C^2` regularity hold by the `ShellField` carrier itself. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawPrefix
    (d : ℕ) (gamma : ℝ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  dimension : 2 ≤ d
  gamma_pos : 0 < gamma
  gamma_le_quarter : gamma ≤ (1 : ℝ) / 4
  independent :
    iIndepFun
      (fun k : ℤ ↦ fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦ F k)
      P.toMeasure
  marginal_scaling : ∀ k : ℤ,
    Algsuperdiff.Frozen.Assumptions.ShellField.shellMarginalLaw P k =
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).map
        (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_triadicScale
          gamma k).aemeasurable
-- FROZEN-STATEMENT-END
