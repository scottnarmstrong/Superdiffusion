import Algsuperdiff.Frozen.Section24.CoarseMatrixDerivative

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_characterization
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U) :
    IsSymmetricBlockMat
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative U a h) ∧
      (∀ p q : Vec d, ∀ vAdj : Solution U a.transpose, ∀ v : Solution U a,
        IsResponseMaximizer U a.transpose p q vAdj →
        IsResponseMaximizer U a p (-q) v →
        blockVecDot (p, q)
            (blockMatVecMul
              (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative U a h) (p, q)) =
          average U (fun x =>
            vecDot (vAdj.toH1.grad x)
              (matVecMul (h.1 x) (v.toH1.grad x)))) ∧
      ∀ D : BlockMat d, IsSymmetricBlockMat D →
        (∀ p q : Vec d, ∀ vAdj : Solution U a.transpose, ∀ v : Solution U a,
          IsResponseMaximizer U a.transpose p q vAdj →
          IsResponseMaximizer U a p (-q) v →
          blockVecDot (p, q) (blockMatVecMul D (p, q)) =
            average U (fun x =>
              vecDot (vAdj.toH1.grad x)
                (matVecMul (h.1 x) (v.toH1.grad x)))) →
          D = Algsuperdiff.Frozen.Section24.coarseMatrixDerivative U a h
-- FROZEN-STATEMENT-END
    := by
  have hspec :=
    (Classical.choose_spec
      (Algsuperdiff.Frozen.Section24.existsUnique_coarseMatrixDerivative U a h)).1
  refine ⟨hspec.1, hspec.2, ?_⟩
  intro D hDsymm hDformula
  exact
    (Algsuperdiff.Frozen.Section24.existsUnique_coarseMatrixDerivative U a h).unique
      ⟨hDsymm, hDformula⟩ hspec
