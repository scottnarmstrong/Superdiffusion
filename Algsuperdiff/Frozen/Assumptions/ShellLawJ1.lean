import Algsuperdiff.Assumptions.ShellField.LIHLocalSigma
import Algsuperdiff.Assumptions.ShellField.SequenceLaw
import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import Mathlib.Probability.Independence.Basic

open Homogenization MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise

-- FROZEN-STATEMENT-BEGIN
/-- ABK26 (J1): the zero shell is integrable and mean-zero at
every point, invariant in law under every real translation, and has range of
dependence `sqrt d` for the integral-generated local sigma-fields `F(U)` of
the governing homogenization-manuscript convention. -/
structure Algsuperdiff.Frozen.Assumptions.ShellLawJ1
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d)) : Prop where
  integrable : ∀ x : Vec d,
    Integrable
      (fun F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d ↦ F 0 x)
      P.toMeasure
  mean_zero : ∀ x : Vec d,
    ∫ F : ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d, F 0 x ∂P.toMeasure = 0
  stationary : ∀ z : Vec d,
    Measure.map
        (Algsuperdiff.Frozen.Assumptions.ShellField.translate z)
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure =
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure
  range_dependence : ∀ (U V : Set (Vec d)),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
        Real.sqrt (d : ℝ) ≤ Homogenization.Book.Ch02.vecNorm (x - y)) →
      Indep
        (Algsuperdiff.Frozen.Assumptions.ShellField.lihLocalSigma U)
        (Algsuperdiff.Frozen.Assumptions.ShellField.lihLocalSigma V)
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure
-- FROZEN-STATEMENT-END
