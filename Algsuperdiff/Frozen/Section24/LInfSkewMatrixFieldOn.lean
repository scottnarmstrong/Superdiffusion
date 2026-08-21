import Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn

open Homogenization Homogenization.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
def Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn {d : ℕ}
    (U : Domain d) :=
  { h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U //
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), symmPart (h.1 x) = 0 }
-- FROZEN-STATEMENT-END
