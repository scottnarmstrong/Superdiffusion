import Algsuperdiff.Section24.Sensitivity.Vocabulary

open Algsuperdiff.Frozen.Section24
open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- Unconditional sensitivity of `lambda_{t,q}`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.lambda_sensitivity_unconditional {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (s t : ℝ) (q : Book.Ch02.MultiscaleExponent),
      0 < s → s ≤ 1 / 4 → 0 < t → t ≤ 1 / 4 → q.IsAdmissible →
      (unitCubeLambda t q
        (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1))⁻¹
        ≤ 6 * Real.rpow
          (1 + C * h.gradientW1Infinity *
            (unitCubeLambda s (.finite 2) a)⁻¹)
          (2 * t / (1 - 2 * s)) *
          (unitCubeLambda t q a)⁻¹
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.lambda_sensitivity_unconditional
    dimension
