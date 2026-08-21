import Algsuperdiff.Section24.Sensitivity.Vocabulary

open Algsuperdiff.Frozen.Section24
open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- Conditional sensitivity of the response functional. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.responseJ_sensitivity {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (p q : Vec d) (δ : ℝ), 0 < δ → δ ≤ 1 →
      responseJ (cubeDomain (originCube d 0))
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1) p q
        ≤ (1 + δ + C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            responseJ (cubeDomain (originCube d 0)) a p q +
          C * δ⁻¹ * (vecNormSq p * h.w1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ +
            |vecDot p q| * h.gradientW1Infinity ^ 2 *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ ^ 2)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.Response.responseJ_sensitivity dimension
