/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.AntisymmetricShift
import Algsuperdiff.Section4.Support.ErrorAtoms

/-!
# The antisymmetric shift at the manuscript's own constant

`AntisymmetricShift.lean` proves the invariance for an arbitrary constant skew
matrix.  This module instantiates it at the manuscript's own constant

```text
  ã_{L,n+2} := a_L − (k_L − k_{n+2})_{z+□_{n+2}} ,
```

i.e. at `Support.fluxCorrectedField`, whose subtracted matrix
`Support.fluxIncrementAverage` is skew because every stream shell is
(`a.shell.antisymmetry`).  The result is the exact display:

```text
  -∇·ã_{L,n+2}∇u = -∇·a_L∇u = ∇·g   in □_m .
```

## References

* ABK26, `l.harmonic.approximation.good.scales`.
* ABK26, (the `ν|∇u|²` energy reading).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The manuscript's constant is skew -/

/-- The averaged flux increment `(k_L − k_m)_Q` is antisymmetric, in the
`matTranspose` spelling the shift lemmas consume.  Disclosed duplicate: see the
module docstring. -/
theorem matTranspose_fluxIncrementAverage (M : ABKModel d) (L k : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    matTranspose (Support.fluxIncrementAverage M L k Q omega) =
      -Support.fluxIncrementAverage M L k Q omega := by
  ext i j
  show Support.fluxIncrementAverage M L k Q omega j i =
    -Support.fluxIncrementAverage M L k Q omega i j
  exact Support.fluxIncrementAverage_skew M L k Q omega i j

/-- The flux-corrected field is literally the cutoff field minus that
constant. -/
theorem fluxCorrectedField_eq_sub_const (M : ABKModel d) (L k : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    Support.fluxCorrectedField M L k Q omega =
      fun x => (Cutoff.coefficientCutoff M.nu L omega).toCoeffField x -
        Support.fluxIncrementAverage M L k Q omega :=
  rfl

/-! ## 2. The equation at the shifted field -/

/-- **`-∇·ã_{L,k}∇u = -∇·a_L∇u`** — the first equality of the printed display,
at the manuscript's own constant, as an identity of the two weak operators
tested against `H¹₀(U)`. -/
theorem integral_vecDot_matVecMul_fluxCorrectedField_eq {U : Set (Vec d)}
    (M : ABKModel d) (L k : ℤ) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d)
    (u : H1Function U) (phi : H10Function U) :
    ∫ x in U, vecDot (matVecMul (Support.fluxCorrectedField M L k Q omega x) (u.grad x))
        (phi.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot
        (matVecMul ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x) (u.grad x))
        (phi.toH1Function.grad x) ∂MeasureTheory.volume :=
  integral_vecDot_matVecMul_sub_const_eq_of_skew
    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
    (matTranspose_fluxIncrementAverage M L k Q omega) u phi

/-- **`-∇·ã_{L,k}∇u = ∇·g` on any set on which `-∇·a_L∇u = ∇·g`**.  No hypothesis
on the set, the solution or the forcing. -/
theorem isDivFormWeakSolutionOn_fluxCorrectedField {U : Set (Vec d)}
    (M : ABKModel d) (L k : ℤ) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d)
    {u : H1Function U} {g : Vec d → Vec d}
    (h : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField U u g) :
    Support.IsDivFormWeakSolutionOn (Support.fluxCorrectedField M L k Q omega) U u g := by
  rw [fluxCorrectedField_eq_sub_const M L k Q omega]
  exact isDivFormWeakSolutionOn_sub_const_of_skew
    (matTranspose_fluxIncrementAverage M L k Q omega) h

/-- The invariance as an equivalence at the manuscript's constant. -/
theorem isDivFormWeakSolutionOn_fluxCorrectedField_iff {U : Set (Vec d)}
    (M : ABKModel d) (L k : ℤ) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d)
    {u : H1Function U} {g : Vec d → Vec d} :
    Support.IsDivFormWeakSolutionOn (Support.fluxCorrectedField M L k Q omega) U u g ↔
      Support.IsDivFormWeakSolutionOn
        (Cutoff.coefficientCutoff M.nu L omega).toCoeffField U u g := by
  rw [fluxCorrectedField_eq_sub_const M L k Q omega]
  exact isDivFormWeakSolutionOn_sub_const_of_skew_iff
    (matTranspose_fluxIncrementAverage M L k Q omega)

/-- **The §4.3 Dirichlet problem at the shifted field.**  The frozen theorem's own
hypothesis `IsDirichletSolutionOn a_L □_m u h g` yields the same Dirichlet
problem for `ã_{L,k}`: the boundary clause constrains only `u - h`. -/
theorem isDirichletSolutionOn_fluxCorrectedField {R : TriadicCube d}
    (M : ABKModel d) (L k : ℤ) (Q : TriadicCube d) (omega : Cutoff.CutoffSample d)
    {u h : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField R u h g) :
    Support.IsDirichletSolutionOn (Support.fluxCorrectedField M L k Q omega) R u h g :=
  ⟨hsol.1, isDivFormWeakSolutionOn_fluxCorrectedField M L k Q omega hsol.2⟩

/-! ## 3. The energy readings of the shifted field -/

/-- The quadratic form of `ã_{L,k}` is that of `a_L`: the shift is invisible to
the energy. -/
theorem vecDot_matVecMul_fluxCorrectedField_self (M : ABKModel d) (L k : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x v : Vec d) :
    vecDot (matVecMul (Support.fluxCorrectedField M L k Q omega x) v) v =
      vecDot (matVecMul (Cutoff.coefficientCutoff M.nu L omega x) v) v :=
  vecDot_matVecMul_sub_const_self_of_skew
    (matTranspose_fluxIncrementAverage M L k Q omega)
    (Cutoff.coefficientCutoff M.nu L omega x) v

/-- **The symmetric part of `ã_{L,k}` is exactly `ν Id`.**  Public re-derivation
(disclosed duplicate) of the `private` `Support.symmPart_fluxCorrectedField`. -/
theorem symmPart_fluxCorrectedField_eq (M : ABKModel d) (L k : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    symmPart (Support.fluxCorrectedField M L k Q omega x) = M.nu • (1 : Mat d) := by
  rw [show Support.fluxCorrectedField M L k Q omega x =
      Cutoff.coefficientCutoff M.nu L omega x -
        Support.fluxIncrementAverage M L k Q omega from rfl,
    symmPart_sub_const_of_skew (matTranspose_fluxIncrementAverage M L k Q omega)]
  exact Cutoff.symmPart_coefficientCutoff M.nu L omega x

theorem vecDot_matVecMul_symmPart_fluxCorrectedField (M : ABKModel d) (L k : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x v : Vec d) :
    vecDot v (matVecMul (symmPart (Support.fluxCorrectedField M L k Q omega x)) v) =
      M.nu * vecNormSq v := by
  rw [symmPart_fluxCorrectedField_eq M L k Q omega x]
  have hmat : matVecMul (M.nu • (1 : Mat d)) v = M.nu • v := by
    rw [smul_matVecMul]
    congr 1
    funext i
    simp only [matVecMul, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i v]
    simp
  rw [hmat]
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
