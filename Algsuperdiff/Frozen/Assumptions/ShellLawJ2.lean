import Algsuperdiff.Assumptions.ShellField.J2Observable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- ABK26 (J2): the exact strict Gaussian tail for the three
weighted essential-`L∞` cube norms.  The author-approved qualitative `C^2`
regularity is already enforced by the shell carrier and is not repeated as a
hypothesis. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawJ2
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  gaussian_tail : ∀ t : ℝ, 1 ≤ t →
    P.toMeasure
        {F | t < Algsuperdiff.Frozen.Assumptions.ShellField.j2Observable d (F 0)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2)))
-- FROZEN-STATEMENT-END
