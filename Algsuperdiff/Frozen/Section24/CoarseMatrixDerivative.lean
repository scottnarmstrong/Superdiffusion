import Algsuperdiff.Frozen.Section24.ExistsUniqueCoarseMatrixDerivative

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U) : BlockMat d :=
  Classical.choose
    (Algsuperdiff.Frozen.Section24.existsUnique_coarseMatrixDerivative U a h)
-- FROZEN-STATEMENT-END
