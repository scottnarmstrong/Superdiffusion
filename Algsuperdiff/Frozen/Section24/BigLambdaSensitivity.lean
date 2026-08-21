import Algsuperdiff.Section24.Sensitivity.Vocabulary

open Algsuperdiff.Frozen.Section24
open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- Fixed-factor sensitivity of `Lambda_{s,2}`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.bigLambda_sensitivity {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d),
      h.gradientW1Infinity ≤ C⁻¹ * unitCubeLambda (3 / 8) (.finite 2) a →
      ∀ (s : ℝ), 0 < s → s < 3 / 8 →
      unitCubeBigLambda s (.finite 2)
          (perturbCoeffOn (cubeDomain (originCube d 0)) a h.toLInfSkewMatrixFieldOn 1)
        ≤ 4 * unitCubeBigLambda s (.finite 2) a +
          C * (3 / 8 - s)⁻¹ * h.w1Infinity ^ 2 *
            (unitCubeLambda s (.finite 2) a)⁻¹
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.bigLambda_sensitivity dimension
