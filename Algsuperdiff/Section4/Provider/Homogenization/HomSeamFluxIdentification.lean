/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Support.FluxCorrectedTwoScaleCarrier
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxCoreSupply

/-!
# The coefficient input of the `ã` seam, PRODUCED

## What this file settles

`HomSeamFluxCoefficient.FluxCorrectedParentIdentification` — the ONE honest
coefficient input of the print-accurate `ã_{L,m}` chain, i.e. the standing
`bounds_mathcal_E_aL` provider obligation restricted to one sample — is
DISCHARGED almost surely:

```text
  ∀ᵐ ω ∂ cutoffSampleLaw M, FluxCorrectedParentIdentification M m (homK M) ω.
```

It is not a commutation, and it is not pointwise: it is produced on the
countable intersection over `L ≥ m` of the coarse-block events.  The four
obstructions are settled as follows.

* **INDEX.**  The obligation's truncation index is `n = m − k` (`homN M m`),
  not the matched index `n = m` of the one-argument chain.  The
  two-argument carrier theorem (`Support.FluxCorrectedTwoScaleCarrier`,
  `ae_forall_parentTruncatedTwo_fluxCorrected_eq_representative`)
  carries every `n ≤ m`, so the two ranges are LITERALLY the same range here
  (`(originCube d m).scale − (homK M: ℤ)` is `homN M m` by `rfl`) and the
  relation is an EQUALITY, not a domination; the domination is only the final
  `L ≥ m` supremum step.
* **SUMMABILITY.**  No summability hypothesis is needed: `CoarseGraining`'s own
  `parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal` already
  performs the `ℝ≥0∞ → ℝ` conversion, and it discharges summability internally
  from the uniform response bound of the parent `CoeffOn`'s ellipticity
  constants (`summable_rootPointwise_infinity_two_terms`).  So the real square
  root never junks to `0`, and the moment anchor is NOT consumed here.
* **FAMILY.**  `rootPointwiseCoeffFamily` versus `fluxCorrectedCoeffFamily`:
  the congruence is proved in this repo as
  `Support.normalizedBlockResponseMax_congr_of_aeeq`, from `CoarseGraining`'s
  `Ch02.doubledResponseJ_eq_ofAEEq`.  No non-a.e.-invariant step appears: the
  response reads the coefficient only through its a.e. class.
* **SIGMA PIN.**  Pinned in `HomSeamFluxCoefficient`: the identification is
  typed at `Annealed.sigmaBar M m`, the pin its right-hand observable already
  carried.

## What is supplied downstream

`RecutCoreSupplyFluxEnergy` is `HomSeamFluxCoreSupply.RecutCoreSupplyFlux` with
the identification conjunct removed — exactly the remaining residue —
and `recutCoreSupplyFlux_of_energy` re-attaches the conjunct by one
application.  `ae_recutCoreSupplyFlux_of_energy` states the a.e. event ONCE, on
the one measure `cutoffSampleLaw M`.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The a.e. production -/

/-- **THE COEFFICIENT INPUT, PRODUCED.**

Almost surely, at every admissible `L` and every fractional order,
`CoarseGraining`'s literal `q = 2` truncated parent error of the printed
flux-corrected field `ã_{L,m}` on `□_m`, truncated at the mesoscale `n = m −
k`, is below the measurable two-argument flux-corrected observable at the same
order.

The `L`-term is in fact an EQUALITY with the observable's `L`-th entry
(`Support.ae_forall_parentTruncatedTwo_fluxCorrected_eq_representative`); the
`≤` is only the passage to the supremum over `L ≥ m`. -/
theorem ae_fluxCorrectedParentIdentification [NeZero d] (M : ABKModel d) (m : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      FluxCorrectedParentIdentification M m (homK M) omega := by
  filter_upwards [ae_forall_parentTruncatedTwo_fluxCorrected_eq_representative M m
    ((originCube d m).scale - ((homK M : ℕ) : ℤ)) (recutParentScale m (homK M))]
    with omega homega L hL t
  rw [homega L hL t]
  exact le_fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) ⟨t.1, t.2.1⟩ omega hL

/-! ## 2. The supply interface -/

/-- **The remaining residue**: `RecutCoreSupplyFlux` with the
coefficient conjunct removed.  Every other character of the statement is
byte-identical to the supply, including the `σ̄_m` pin. -/
def RecutCoreSupplyFluxEnergy [NeZero d] (M : ABKModel d)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (Cen0 : ℝ)
    (hd1 : 1 ≤ d) (hlog : 4 ≤ |Real.log M.gamma|)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => ((Annealed.sigmaBar M m : ℝ)) • (1 : Mat d))
        (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      ∃ (S : ℝ) (Fflux : Vec d → Vec d),
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m)
              (recutExponent d hd1).exponent.toReal (homS M - homS M / 4) (homK M) N
              (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) ≤
            S) ∧
        S ≤ Cen0 * recutEnergyFactor M Y m omega *
            energyBracket ((Annealed.sigmaBar M m : ℝ))
              (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingFinitePMultiscale (originCube d m) (homK M)
            (recutPinnedCcgFlux d (recutExponent d hd1)) (homS M) (homS M / 4)
            (recutOrderTop : FractionalOrder).1 (recutExponent d hd1).exponent.toReal
            ((Annealed.sigmaBar M m : ℝ))
            (recutPinnedE1Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedDg m recutOrderTop (recutExponent d hd1) g)
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux)

/-- **THE ONE-APPLICATION HANDOFF.**  The energy residue plus the coefficient
input IS the supply, in exactly the shape
`HomSeamFluxCoreSupply.spineDatumRecutCoreFlux_of_supply` consumes. -/
theorem recutCoreSupplyFlux_of_energy [NeZero d] (M : ABKModel d)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (Cen0 : ℝ)
    (hd1 : 1 ≤ d) (hlog : 4 ≤ |Real.log M.gamma|) (omega : Cutoff.CutoffSample d)
    (henergy : RecutCoreSupplyFluxEnergy M Y m Cen0 hd1 hlog omega)
    (hid : FluxCorrectedParentIdentification M m (homK M) omega) :
    RecutCoreSupplyFlux M Y m Cen0 hd1 hlog omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨S, Fflux, hS0, hS, hSbound, hCGm⟩ :=
    henergy L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  exact ⟨S, Fflux, hS0, hS, hSbound, hCGm, hid⟩

/-- **THE SUPPLY, A.E.**  One theorem, one measure: whenever the energy residue
holds almost surely, the full `ã` supply does. -/
theorem ae_recutCoreSupplyFlux_of_energy [NeZero d] (M : ABKModel d)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (Cen0 : ℝ)
    (hd1 : 1 ≤ d) (hlog : 4 ≤ |Real.log M.gamma|)
    (henergy : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      RecutCoreSupplyFluxEnergy M Y m Cen0 hd1 hlog omega) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      RecutCoreSupplyFlux M Y m Cen0 hd1 hlog omega := by
  filter_upwards [henergy, ae_fluxCorrectedParentIdentification M m] with omega he hi
  exact recutCoreSupplyFlux_of_energy M Y m Cen0 hd1 hlog omega he hi

end

end Algsuperdiff.Section4.Provider.Homogenization
