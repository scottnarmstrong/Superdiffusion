import Algsuperdiff.Section24.Sensitivity.Vocabulary

open Algsuperdiff.Frozen.Section24
open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- Conditional sensitivity of `lambda_{s,q}`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.lambda_sensitivity {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (s : ℝ) (q : Book.Ch02.MultiscaleExponent),
        0 < s → s ≤ 1 / 2 → q.IsAdmissible →
        (unitCubeLambda s q
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1))⁻¹
          ≤ (1 + C * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            (unitCubeLambda s q a)⁻¹
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.Lambda.lambda_sensitivity dimension
