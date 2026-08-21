import Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.BigLambda.ExistsUniqueUnitCubeBigLambda

open Homogenization Homogenization.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section24.unitCubeBigLambda
    {d : ℕ} (s : ℝ) (q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) : ℝ :=
  Classical.choose
    (Algsuperdiff.Frozen.Section24.existsUnique_unitCubeBigLambda
      s q a)
-- FROZEN-STATEMENT-END
