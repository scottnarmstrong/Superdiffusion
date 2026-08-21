import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public

open Homogenization Homogenization.Book.Ch02

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section24.matrixDerivativeNorm {d : ℕ}
    (D : Vec d →L[ℝ] Mat d) : ℝ :=
  sSup (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} => matrixNorm (D v.1))
-- FROZEN-STATEMENT-END
