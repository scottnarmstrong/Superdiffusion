import Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn
import Homogenization.Sobolev.PotentialSolenoidalL2

/-!
# Bounded perturbations for the coarse-matrix derivative

The source carrier is frozen in `LInfMatrixFieldOn`.  This module records the
two analytic consequences needed by the construction of `D_h`: an `L∞` matrix
field maps vector `L²` fields to vector `L²`, and hence the exact displayed
pairing in `e.def.Dh` is integrable for arbitrary solutions.
-/

namespace Algsuperdiff.Section24

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

theorem memVectorL2_matVecMul_of_lInfMatrixFieldOn
    (U : Domain d) (h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U)
    {f : Vec d → Vec d} (hf : MemVectorL2 (U : Set (Vec d)) f) :
    MemVectorL2 (U : Set (Vec d)) (fun x => matVecMul (h.1 x) (f x)) := by
  rw [MemVectorL2] at hf ⊢
  refine (memLp_pi_iff).2 ?_
  intro i
  have hsum :
      MemLp (fun x : Vec d => ∑ j : Fin d, h.1 x i j * f x j) 2
        (volumeMeasureOn (U : Set (Vec d))) := by
    refine memLp_finset_sum (s := Finset.univ)
      (f := fun j => fun x : Vec d => h.1 x i j * f x j) ?_
    intro j _
    exact ((memLp_pi_iff.mp hf) j).mul' (h.2 i j)
  simpa [matVecMul] using hsum

end

end Algsuperdiff.Section24
