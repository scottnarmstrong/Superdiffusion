import Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.UnitCubeHomogenizationError

/-! # Characterization of the origin-cube homogenization error -/

namespace Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError

open Homogenization Homogenization.Book.Ch02 MeasureTheory

variable {d : ℕ}

/-- The unique-choice characterization used by the corresponding frozen
theorem. -/
theorem characterization [NeZero d]
    (s : ℝ) (p q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) (a0 : Mat d) :
    ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
          s p q a a0 =
          Book.Ch02.HomogenizationErrorOnCube
            (originCube d 0) s p q F a0 :=
  (Classical.choose_spec
    (Algsuperdiff.Frozen.Section24.existsUnique_unitCubeHomogenizationError
      s p q a a0)).1

end Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError
