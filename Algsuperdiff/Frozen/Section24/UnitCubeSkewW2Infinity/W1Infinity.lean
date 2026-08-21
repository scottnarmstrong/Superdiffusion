import Algsuperdiff.Frozen.Section24.MatrixDerivativeNorm
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.w1Infinity
    {d : ℕ} (h : Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity d) : ℝ :=
  max
    (ENNReal.toReal
      (eLpNorm (fun x => Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
          (h.firstDeriv x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))))
    (ENNReal.toReal
      (eLpNorm (fun x => matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))))
-- FROZEN-STATEMENT-END
