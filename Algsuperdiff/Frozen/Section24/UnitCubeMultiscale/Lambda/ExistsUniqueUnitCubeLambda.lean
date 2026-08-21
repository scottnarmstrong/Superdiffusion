import Algsuperdiff.Section24.UnitCubeMultiscale.Lambda.WellDefinedness

open Homogenization Homogenization.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.existsUnique_unitCubeLambda
    {d : ℕ} (s : ℝ) (q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    ∃! value : ℝ, ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        value = Book.Ch02.lambdaSq (originCube d 0) s q F
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.UnitCubeMultiscale.Lambda.existsUnique s q a
