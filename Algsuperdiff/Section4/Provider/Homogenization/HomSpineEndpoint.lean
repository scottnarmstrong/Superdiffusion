/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomStepFourEnergy
import Algsuperdiff.Section3.Cutoff.Limit

/-!
# Theorem B, §4.5: the Step-4 endpoint at the anchor's own carriers

## What this is

`HomStepFourEnergy.stepFourEnergyDisplay` composed onto the exact carriers the
frozen root's clause (C4) uses:

* the coefficient field is the cutoff field `a_L(ω) = ν Id + κ_L(ω)`
  (`Cutoff.coefficientCutoff M.nu L omega`), whose symmetric part is `ν Id`
  (`Cutoff.symmPart_coefficientCutoff`) — so the `ν`-drop fires by name and the
  left-hand side is literally the root's `⨍ ν|∇u|²`;
* the comparator field is the scalar `σ̄_m Id`, the root's own spelling;
* the window is `openCubeSet (originCube d m)`;
* the data bracket is the root's own
  `(√σ̄⁻¹ 3^{m/2} K_g + √σ̄ (K_h^∞ + 3^{m/2} K_h))²`.

## The conditional set of this endpoint (itemized)

Beyond the standard frame (the two Dirichlet-problem hypotheses of the
introduction's Dirichlet-pair display, `0 < σ̄_m`, and the three `H¹`-level
integrability facts), there are exactly THREE mathematical inputs, all
transcribed:

1. `hWf`, `hWg` — the flux and gradient weak bounds.  These are the two halves
   of ONE application of the general coarse-graining proposition (printed at
   finite `p ∈ [2,∞)` with `C(p,d)`, the two halves summed on the left), read
   off as the manuscript instructs.  They are ONE source hypothesis `hCG`, split
   here only because the two summands of the energy split consume them
   separately.
2. `hSch` — the Schauder bound on `‖∇v‖_{W̲^{s,∞}(□_m)}`.
   The Schauder gap, bullet 2: asserted with no citation, no
   labelled in-paper result and no bibliography key; not proved in this
   repository or in `CoarseGraining`.  It is a THIRD conditional, disclosed, NOT reducible
   to `{hC, hCG}`.

`hC` (Theorem C) does not appear here: it is consumed upstream, inside the
`EB` witness (Steps 1--3).  So the Step-4 leg of the spine is conditional on
`{hCG, hSch}` and the frame, and the full clause-(C4) chain is conditional on
`{hC, hCG, hSch}`.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- **The Step-4 endpoint, at the frozen root's clause-(C4) shape.**

Every object is the root's own: the cutoff coefficient field, the scalar
comparator, the origin cube at scale `m`, and the square of the root's data
bracket.  The residual constant `2 C_w C_sch` is exactly what's witness
rescaling (`ethmB_const_smul_moment`) absorbs into `EthmB(m)`.

Conditional set: `{hWf, hWg}` (= the ONE the general coarse-graining proposition
application) and `hSch` (the Schauder gap), plus the frame. -/
theorem stepFourEnergyEndpoint (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {sigmaBarM s Kg Kh KhInf Cw Csch EB Ksup KHol : ℝ}
    {u v h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsig : 0 < sigmaBarM) (hCw : 0 ≤ Cw) (hEB : 0 ≤ EB)
    (hD : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hsup : 0 ≤ Ksup) (hhol : 0 ≤ KHol)
    (hsol : IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u h g)
    (hcomp : IsDirichletSolutionOn
      (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g)
    (hiU : IntegrableOn (fun x => vecDot (u.grad x)
      (matVecMul ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x) (u.grad x)))
      (openCubeSet (originCube d m)) volume)
    (hiV : IntegrableOn (fun x => vecDot (v.grad x) (sigmaBarM • v.grad x))
      (openCubeSet (originCube d m)) volume)
    (hiC : IntegrableOn (fun x => vecDot
      (matVecMul ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x) (u.grad x))
      (v.grad x)) (openCubeSet (originCube d m)) volume)
    (hb : ∀ x ∈ openCubeSet (originCube d m), ‖v.grad x‖ ≤ Ksup)
    (hH : HolderSeminormBoundOn (openCubeSet (originCube d m)) s KHol v.grad)
    (hSch : wsInftyGauge (originCube d m) s Ksup KHol ≤
      Csch * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
        dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hWf : WeakNegDualBoundOn (originCube d m) s
      (Real.rpow 3 (s * (m : ℝ)) * sigmaBarM *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
      (fun x => matVecMul ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x)
        (u.grad x) - sigmaBarM • v.grad x))
    (hWg : WeakNegDualBoundOn (originCube d m) s
      (Real.rpow 3 (s * (m : ℝ)) *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
      (fun x => u.grad x - v.grad x)) :
    |volumeAverage (openCubeSet (originCube d m))
          (fun y => M.nu * vecNormSq (u.grad y)) -
        volumeAverage (openCubeSet (originCube d m))
          (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
      2 * Cw * Csch * EB *
        (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
            Real.sqrt sigmaBarM * (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ) := by
  have hsym : ∀ x : Vec d,
      symmPart ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x) =
        (M.nu : ℝ) • (1 : Mat d) := fun x =>
    Cutoff.symmPart_coefficientCutoff M.nu L omega x
  have hscale : ((originCube d m).scale : ℤ) = m := rfl
  have hsplit := energy_split (A := (Cutoff.coefficientCutoff M.nu L omega).toCoeffField)
    (Qc := originCube d m) (sigma := sigmaBarM) (nu := (M.nu : ℝ)) (u := u) (v := v)
    (h := h) (g := g)
    (F := fun x => matVecMul ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField x)
      (u.grad x))
    (fun _ => rfl) hsym hsol.2 hcomp.2 hsol.1 hcomp.1 hiU hiV hiC
  exact stepFourEnergyDisplay hsig hCw hEB hD hsup hhol hsplit hb hH hSch hWf hWg

end

end Algsuperdiff.Section4.Provider.Homogenization
