import Homogenization.Book.Ch02.Setup

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
def Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn {d : ℕ}
    (U : Domain d) :=
  { h : CoeffField d // ∀ i j : Fin d,
    MemLp (fun x : Vec d => h x i j) ∞
      (volumeMeasureOn (U : Set (Vec d))) }
-- FROZEN-STATEMENT-END
