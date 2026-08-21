import Algsuperdiff.Section24.Sensitivity.Vocabulary

open Algsuperdiff.Frozen.Section24
open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- The directional derivative identity for the response functional. -/
-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.responseJ_derivative {d : ℕ}
    (dimension : 2 ≤ d) (U : Domain d) (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (p q : Vec d) :
    HasDerivAt
      (fun t => responseJ U (perturbCoeffOn U a h t) p q)
      ((1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -q))) 0
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.Sensitivity.Provider.Path.responseJ_derivative
    dimension U a h p q
