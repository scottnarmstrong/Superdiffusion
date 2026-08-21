import Algsuperdiff.Frozen.Section24.MatrixDerivativeNorm
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.valueL2
    {d : ℕ} (h : Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity d) : ℝ :=
  ENNReal.toReal
    (eLpNorm (fun x => matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)) 2
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))))
-- FROZEN-STATEMENT-END
