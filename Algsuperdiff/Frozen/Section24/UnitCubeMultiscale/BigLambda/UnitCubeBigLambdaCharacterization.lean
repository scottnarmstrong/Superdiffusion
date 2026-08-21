import Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.Characterization

open Homogenization Homogenization.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section24.unitCubeBigLambda_characterization
    {d : ℕ} (s : ℝ) (q : Book.Ch02.MultiscaleExponent)
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    ∀ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a →
        Algsuperdiff.Frozen.Section24.unitCubeBigLambda s q a =
          Book.Ch02.LambdaSq (originCube d 0) s q F
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.characterization s q a
