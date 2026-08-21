/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.NuIdentification
import Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestriction
import Algsuperdiff.Section3.Cutoff.CoefficientFamily

/-!
# Theorem B, §4.5, Step 2: the `ν`-drop and the Dirichlet carrier entry

## The two obstructions closed here

The obstructions (1) and (2) of Step 2.

**(1) THE `ν`-DROP** ("the left-hand side
`ν^{1/2}‖∇u‖_{L̲²}` is the symmetric-coefficient energy for `a_L = ν Id + κ`").
`CoarseGraining` prices a Dirichlet solution by `h1EnergyNormOnCube`, i.e. by the square root
of the SYMMETRIC-part energy `⨍_□ ∇u · symm(a) ∇u`.  Step 2's display carries
`ν^{1/2}‖∇u‖_{L̲²(□_m)}`.  The two agree because `symm(a_L) = ν Id` exactly:
the cutoff field is `ν Id + κ_L` with `κ_L` skew.

Already available (adapted, not re-derived): `Cutoff.symmPart_coefficientCutoff`
(the pointwise identity at the FIELD), `localizedCoeffEnergyValue_eq_mul_of_
symmPart_eq` (the generic drop), and the drops at the flux-corrected and
parent-rebased families.  MISSING and supplied here: the drop at the TRIADIC
FAMILY `Cutoff.coefficientCutoffTriadicCoeffFamily`, which is the family a
`Ch03.DirichletForcedCubeSolution` is indexed by, together with the `√`-split
that produces the printed `ν^{1/2} · ‖∇u‖_{L̲²}` product rather than
`√(ν · ⨍|∇u|²)`.

**(2) THE CARRIER ENTRY.**  `Support.IsDirichletSolutionOn a Q u h g` (the §4.3
carrier, a conjunction) versus `Ch03.DirichletForcedCubeSolution Q A g` (`CoarseGraining`'s
structure, the object `energyConsequencesRHSTheory` prices).  The structure map
is supplied here in both useful directions:

* `dirichletForcedCubeSolutionOfIsDirichletSolutionOn` — the entry, at the
  NEGATED forcing;
* `isDivFormWeakSolutionOn_of_dirichletForcedCubeSolution` — the exit, at the
  equation half only.  The boundary half does not come back: `CoarseGraining`'s
  zero-trace field is a.e. while the §4.3 carrier's is exact, so the exit
  direction cannot recover the pointwise witness.

## Sign convention (the only subtlety)

`Support.IsDivFormWeakSolutionOn` renders `-∇·a∇u = ∇·g` as
`∫ a∇u·∇φ = -∫ g·∇φ` (the distributional convention), while `CoarseGraining`'s
`Ch03.IsForcedEquation` renders the same equation as `∫ a∇u·∇φ = +∫ g·∇φ`.  The
two therefore correspond at the negated forcing, exactly as
`Support/Dirichlet.lean`'s module docstring records for the sibling zero-trace
surface.  The entry map produced here lands in
`DirichletForcedCubeSolution Q A (fun x => -g x)`.  Every Step-2 leg is a
SEMINORM of the datum, invariant under `g ↦ -g`, so the display is unaffected;
the negation is nevertheless carried visibly and never absorbed.

## The boundary witness

`Support.HasZeroTraceDifferenceOn` carries the `H¹₀` witness with POINTWISE
identities `u = h + w`, `∇u = ∇h + ∇w`; `CoarseGraining`'s
`zeroTraceDifference` field asks only for `w =ᵐ u - h` on the cube.  The entry
map therefore only weakens, via `Filter.Eventually.of_forall`; nothing is
assumed.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The `ν`-drop at the cutoff triadic family -/

/-- **`symm(a_L) = ν Id` at the triadic family.**  The family's coefficient on
every cube is the same pointwise field `ν Id + κ_L`, so the pointwise
identity transports by `rfl`. -/
theorem symmPart_coefficientCutoffTriadicCoeffFamily (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) (y : Vec d) :
    symmPart
        (((Cutoff.coefficientCutoffTriadicCoeffFamily M L omega).coeffOn Q).toCoeffField y) =
      (M.nu : ℝ) • (1 : Mat d) :=
  Cutoff.symmPart_coefficientCutoff M.nu L omega y

/-- **The `ν`-drop at the cutoff family**: the localized coefficient energy of
`a_L` is exactly `ν` times the normalized gradient `L²` square. -/
theorem localizedCoeffEnergyValue_coefficientCutoffTriadicCoeffFamily_eq (M : ABKModel d)
    (L : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) (V : Set (Vec d))
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedCoeffEnergyValue V
        ((Cutoff.coefficientCutoffTriadicCoeffFamily M L omega).coeffOn Q) u =
      (M.nu : ℝ) * normalizedSetAverage V (fun y => vecNormSq (u.grad y)) :=
  localizedCoeffEnergyValue_eq_mul_of_symmPart_eq V _ u (M.nu : ℝ)
    (symmPart_coefficientCutoffTriadicCoeffFamily M L omega Q)

/-- **The printed `ν^{1/2} ‖∇u‖_{L̲²(□)}`.**  `CoarseGraining`'s cube energy norm of `a_L`
factors EXACTLY as `ν^{1/2}` times the normalized gradient `L²` norm — the
left-hand side of the energy-from-data display and of
the mesoscale energy bound. -/
theorem h1EnergyNormOnCube_coefficientCutoffTriadicCoeffFamily_eq (M : ABKModel d)
    (L : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    h1EnergyNormOnCube Q (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) u =
      Real.sqrt (M.nu : ℝ) *
        Real.sqrt (normalizedSetAverage (openCubeSet Q) (fun y => vecNormSq (u.grad y))) := by
  rw [h1EnergyNormOnCube,
    localizedCoeffEnergyValue_coefficientCutoffTriadicCoeffFamily_eq M L omega Q,
    Real.sqrt_mul (le_of_lt M.nu_pos)]

/-! ## 2. The Dirichlet carrier entry -/

/-- **The carrier entry.**  A §4.3 Dirichlet solution `u` of `-∇·A∇u = ∇·g` with
boundary datum `h` IS a `CoarseGraining` `DirichletForcedCubeSolution` for the same `u` and
the same `h`, at the negated forcing.

The four fields: `toH1:= u`; `boundaryData:= h`; `weakSolution` is the
sign-convention converter; `zeroTraceDifference` is the §4.3 witness weakened
from pointwise to a.e.  No analytic content, no existence claim. -/
def dirichletForcedCubeSolutionOfIsDirichletSolutionOn {Q : TriadicCube d}
    {A : CoeffFamily d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((A.coeffOn Q).toCoeffField) Q u h g) :
    DirichletForcedCubeSolution Q A (fun x => -g x) where
  toH1 := u
  boundaryData := h
  weakSolution := isForcedEquation_neg_of_isDivFormWeakSolutionOn hsol.2
  zeroTraceDifference := by
    obtain ⟨w, hval, _⟩ := hsol.1
    refine ⟨w, Filter.Eventually.of_forall fun x => ?_⟩
    simp only [hval x]
    ring

@[simp]
theorem dirichletForcedCubeSolutionOfIsDirichletSolutionOn_toH1 {Q : TriadicCube d}
    {A : CoeffFamily d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((A.coeffOn Q).toCoeffField) Q u h g) :
    (dirichletForcedCubeSolutionOfIsDirichletSolutionOn hsol).toH1 = u := rfl

@[simp]
theorem dirichletForcedCubeSolutionOfIsDirichletSolutionOn_boundaryData {Q : TriadicCube d}
    {A : CoeffFamily d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((A.coeffOn Q).toCoeffField) Q u h g) :
    (dirichletForcedCubeSolutionOfIsDirichletSolutionOn hsol).boundaryData = h := rfl

/-- The exit direction, equation half: `CoarseGraining`'s forced equation is the §4.3 weak
equation at the negated forcing.  (The boundary half cannot be exited: `CoarseGraining`
stores the witness only a.e., the §4.3 carrier demands it pointwise — a genuine
asymmetry of the two carriers.) -/
theorem isDivFormWeakSolutionOn_of_dirichletForcedCubeSolution {Q : TriadicCube d}
    {A : CoeffFamily d} {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q A g) :
    IsDivFormWeakSolutionOn ((A.coeffOn Q).toCoeffField) (openCubeSet Q) v.toH1
      (fun x => -g x) :=
  isDivFormWeakSolutionOn_of_isForcedEquation v.weakSolution

/-! ## 3. The composition: the energy of an entered solution, `ν`-dropped -/

/-- The energy norm `CoarseGraining` prices is the energy norm of the very solution entered:
a definitional identity, recorded so the composition is auditable. -/
theorem dirichletForcedSolutionEnergyNorm_ofIsDirichletSolutionOn {Q : TriadicCube d}
    {A : CoeffFamily d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((A.coeffOn Q).toCoeffField) Q u h g) :
    dirichletForcedSolutionEnergyNorm Q A
        (dirichletForcedCubeSolutionOfIsDirichletSolutionOn hsol) =
      h1EnergyNormOnCube Q A u := rfl

/-- **The Step-2 left-hand side, assembled.**

For the §4.5 field `a_L = ν Id + κ_L`, a §4.3 Dirichlet solution entered into
`CoarseGraining`'s carrier is priced by `CoarseGraining` at exactly

```
  ν^{1/2} ‖∇u‖_{L̲²(□)},
```

which is the left side of the energy-from-data display and of
the mesoscale energy bound.  Blockers (1) and (2) closed in one statement. -/
theorem dirichletForcedSolutionEnergyNorm_coefficientCutoff_eq (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) {Q : TriadicCube d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn
      (((Cutoff.coefficientCutoffTriadicCoeffFamily M L omega).coeffOn Q).toCoeffField)
      Q u h g) :
    dirichletForcedSolutionEnergyNorm Q (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (dirichletForcedCubeSolutionOfIsDirichletSolutionOn hsol) =
      Real.sqrt (M.nu : ℝ) *
        Real.sqrt (normalizedSetAverage (openCubeSet Q) (fun y => vecNormSq (u.grad y))) := by
  rw [dirichletForcedSolutionEnergyNorm_ofIsDirichletSolutionOn hsol,
    h1EnergyNormOnCube_coefficientCutoffTriadicCoeffFamily_eq M L omega Q u]

/-- The same statement entered at the §4.5 spelling of the field: the Dirichlet
carrier of the frozen §4.3 anchors is stated at
`(Cutoff.coefficientCutoff M.nu L omega).toCoeffField`, which is the triadic
family's coefficient on every cube by `rfl`. -/
theorem dirichletForcedSolutionEnergyNorm_coefficientCutoffField_eq (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) {Q : TriadicCube d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField)
      Q u h g) :
    dirichletForcedSolutionEnergyNorm Q (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (dirichletForcedCubeSolutionOfIsDirichletSolutionOn hsol) =
      Real.sqrt (M.nu : ℝ) *
        Real.sqrt (normalizedSetAverage (openCubeSet Q) (fun y => vecNormSq (u.grad y))) :=
  dirichletForcedSolutionEnergyNorm_coefficientCutoff_eq M L omega hsol

end

end Algsuperdiff.Section4.Provider.Homogenization
