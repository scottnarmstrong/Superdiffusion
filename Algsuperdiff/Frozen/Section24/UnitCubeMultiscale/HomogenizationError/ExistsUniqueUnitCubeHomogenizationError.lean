import Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.WellDefinedness

open Homogenization Homogenization.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.existsUnique_unitCubeHomogenizationError
    {d : ℕ} [NeZero d] (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) :
    ∃! value : ℝ, ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        value = Book.Ch02.HomogenizationErrorOnCube
          (originCube d 0) s p q F a0
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.existsUnique
    s p q a a0
