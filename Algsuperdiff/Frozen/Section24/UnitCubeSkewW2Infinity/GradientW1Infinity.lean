import Algsuperdiff.Frozen.Section24.MatrixSecondDerivativeNorm
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
noncomputable def
    Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.gradientW1Infinity
    {d : ℕ} (h : Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity d) : ℝ :=
  max
    (ENNReal.toReal
      (eLpNorm (fun x => Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm
          (h.secondDeriv x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))))
    (ENNReal.toReal
      (eLpNorm (fun x => Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
          (h.firstDeriv x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))))
-- FROZEN-STATEMENT-END
