import Algsuperdiff.Section24.CoarseMatrixDerivative.Existence

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.existsUnique_coarseMatrixDerivative
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U) :
    ∃! D : BlockMat d,
      IsSymmetricBlockMat D ∧
      ∀ p q : Vec d, ∀ vAdj : Solution U a.transpose, ∀ v : Solution U a,
        IsResponseMaximizer U a.transpose p q vAdj →
        IsResponseMaximizer U a p (-q) v →
        blockVecDot (p, q) (blockMatVecMul D (p, q)) =
          average U (fun x =>
            vecDot (vAdj.toH1.grad x)
              (matVecMul (h.1 x) (v.toH1.grad x)))
-- FROZEN-STATEMENT-END
    := by
  exact
    Algsuperdiff.Section24.CoarseMatrixDerivative.Internal.existsUnique_coarseMatrixDerivative
      U a h
