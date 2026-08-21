import Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.BigLambda.UnitCubeBigLambda

/-! # Characterization of origin-cube upper multiscale ellipticity -/

namespace Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda

open Homogenization Homogenization.Book.Ch02 MeasureTheory

variable {d : ℕ}

/-- The unique-choice characterization used by the corresponding frozen
theorem. -/
theorem characterization
    (s : ℝ) (q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        Algsuperdiff.Frozen.Section24.unitCubeBigLambda s q a =
          Book.Ch02.LambdaSq (originCube d 0) s q F :=
  (Classical.choose_spec
    (Algsuperdiff.Frozen.Section24.existsUnique_unitCubeBigLambda s q a)).1

end Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda
