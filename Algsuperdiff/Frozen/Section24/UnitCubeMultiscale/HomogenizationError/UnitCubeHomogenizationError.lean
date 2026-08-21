import Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.ExistsUniqueUnitCubeHomogenizationError

open Homogenization Homogenization.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
    {d : ℕ} [NeZero d] (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) : ℝ :=
  Classical.choose
    (Algsuperdiff.Frozen.Section24.existsUnique_unitCubeHomogenizationError
      s p q a a0)
-- FROZEN-STATEMENT-END
