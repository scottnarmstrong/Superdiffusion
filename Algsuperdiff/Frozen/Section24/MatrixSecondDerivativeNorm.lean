import Algsuperdiff.Frozen.Section24.MatrixDerivativeNorm

open Homogenization Homogenization.Book.Ch02

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm {d : ℕ}
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) : ℝ :=
  sSup (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} =>
    Algsuperdiff.Frozen.Section24.matrixDerivativeNorm (H v.1))
-- FROZEN-STATEMENT-END
