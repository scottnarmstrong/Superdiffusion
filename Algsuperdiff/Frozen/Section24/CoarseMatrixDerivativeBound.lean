import Algsuperdiff.Section24.Sensitivity.Vocabulary

open Algsuperdiff.Frozen.Section24
open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- The unit-cube sensitivity estimate for the coarse-matrix derivative. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_bound {d : ℕ}
    (dimension : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffOn (cubeDomain (originCube d 0)))
      (h : UnitCubeSkewW2Infinity d) (p q : Vec d),
      |blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative (cubeDomain (originCube d 0)) a
          h.toLInfSkewMatrixFieldOn.1) (p, -q))|
        ≤ C * (vecNorm p * h.w1Infinity *
              Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) +
            Real.sqrt |vecDot p q| * h.gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
            Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
          C * h.gradientW1Infinity *
            (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ *
            responseJ (cubeDomain (originCube d 0)) a p q
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.DhBound.coarseMatrixDerivative_bound
    dimension
