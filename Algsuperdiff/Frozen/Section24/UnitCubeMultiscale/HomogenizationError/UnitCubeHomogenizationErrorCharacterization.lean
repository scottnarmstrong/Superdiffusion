import Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.Characterization

open Homogenization Homogenization.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
    {d : ℕ} [NeZero d] (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) :
    ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
          s p q a a0 =
          Book.Ch02.HomogenizationErrorOnCube
            (originCube d 0) s p q F a0
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.characterization
    s p q a a0
