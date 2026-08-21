import Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
import Homogenization.Sobolev.WeakDerivatives

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
structure Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity (d : ℕ) where
  toLInfSkewMatrixFieldOn :
    Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
      (cubeDomain (originCube d 0))
  firstDeriv : Vec d → Vec d →L[ℝ] Mat d
  secondDeriv : Vec d → Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)
  firstDeriv_memLp : ∀ k i j : Fin d,
    MemLp (fun x => firstDeriv x (basisVec k) i j) ∞
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
  secondDeriv_memLp : ∀ l k i j : Fin d,
    MemLp (fun x => secondDeriv x (basisVec l) (basisVec k) i j) ∞
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
  hasWeakPartialDeriv_value : ∀ k i j : Fin d,
    HasWeakPartialDerivOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) k
      (fun x => toLInfSkewMatrixFieldOn.1.1 x i j)
      (fun x => firstDeriv x (basisVec k) i j)
  hasWeakPartialDeriv_firstDeriv : ∀ l k i j : Fin d,
    HasWeakPartialDerivOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) l
      (fun x => firstDeriv x (basisVec k) i j)
      (fun x => secondDeriv x (basisVec l) (basisVec k) i j)
-- FROZEN-STATEMENT-END
