/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.CarrierIdentification

/-!
# The family bridge: the two `ã_{L,m}` carriers at the *block* response level

Nothing here imports that file, and nothing here claims the anchor.

## The gap this closes

The Step-1 endpoint of `Step1ScaleSum.lean` (and hence the whole Step-1/Step-2
chain, and hence the object the a.e.-fidelity certificate of
`TwoScaleFidelity.lean` puts under the anchor's `lintegral`) is written at the
Chapter 4 dependent family of the flux-corrected carrier field,

* `Support.fluxCorrectedCoeffFamily M L m (□_m) ω`,

through the *block* response maximum `Ch02.normalizedBlockResponseMax`.  Step 3
(`Step3HSlot.lean`) speaks instead at the hand-built family

* `Annular.subConstCutoffTriadicCoeffFamily M L (k_L − k_m)_{□_m} … ω`,

because that is the family the proved §4.1 response transport and the Section
2.4 sensitivity anchor consume.

`Annular.CarrierIdentification` connects the two families at ONE cube and at the
`scalarResponseMax` level.  What the Step-1 endpoint needs is the *family*-level
a.e. equality, which upgrades the identification to every object of the Chapter 2
`𝓔`-tower — in particular to `normalizedBlockResponseMax`, the per-cube object of
the endpoint's inner average.  That upgrade is supplied here.

## The route: no new mathematics

`Ch02.TriadicCoeffFamily.A is *defined* as the a.e. equality of the cube
representatives triadic cube, and the proof of
`Annular.fluxCorrectedCoeffFamily_coeffOn_aeeq_subConstCutoff` never looks at
its cube: both `toCoeffField` values reduce definitionally to `x ↦ a_L(x) −
(k_L − k_m)_{□_m}`.  So the same four lines give the family-level statement,
and then CoarseGraining's own a.e.-invariance layer
(`Ch02.normalizedBlockResponseMax_eq_ofA, `Ch02.scaleResponseAtScale_eq_ofA,
`Ch02.HomogenizationError_eq_ofA) transports every level of the tower with no
further work.

## Main results

* `fluxCorrectedCoeffFamily_aeEq_subConstFluxFamily` — the family-level a.e.
  equality of the two `ã_{L,m}` carriers.
* `normalizedBlockResponseMax_fluxCorrected_eq` — **the missing congruence**: the
  per-cube block response maximum of the endpoint is the per-cube block response
  maximum at the family Step 3 speaks, at every cube and every comparator.
* `finsetAverage_rpow_normalizedBlockResponseMax_fluxCorrected_eq` — the same for
  the endpoint's inner `p/2`-average over descendants, verbatim in the shape
  `Step1ScaleSum.step1_scaleSum_endpoint_originCube` produces.
* `homogenizationError_fluxCorrected_eq` — the same for the two-argument
  `(∞, 2)` error itself, i.e. for the object the a.e.-fidelity certificate names.

## References

* ABK26, (`ã_{L,m}`), (`l.bounds.mathcal.E.aL`), (Step 3).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-- The hand-built `ã_{L,m} = a_L − (k_L − k_m)_{□_m}` triadic family, at the
development's origin-cube recentering: a spelling abbreviation for the family
appearing in `Step3HSlot.exists_responseJ_step3_recentered`. -/
def subConstFluxFamily (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) : Ch02.TriadicCoeffFamily d :=
  subConstCutoffTriadicCoeffFamily M L
    (Support.fluxIncrementAverage M L m (originCube d m) omega)
    (matTranspose_fluxIncrementAverage M L m (originCube d m) omega) omega

theorem subConstFluxFamily_eq (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    subConstFluxFamily M L m omega =
      subConstCutoffTriadicCoeffFamily M L
        (Support.fluxIncrementAverage M L m (originCube d m) omega)
        (matTranspose_fluxIncrementAverage M L m (originCube d m) omega) omega :=
  rfl

/-! ## The family-level a.e. identification -/

/-- **The family-level form of A6c finding (f).**  The Chapter 4 dependent family
of the flux-corrected carrier field and the hand-built family of
`a_L − (k_L − k_m)_{□_m}` are a.e. equal **as triadic coefficient families**:
their cube representatives agree at every triadic cube.

This is `Annular.fluxCorrectedCoeffFamily_coeffOn_aeeq_subConstCutoff` with its
cube quantified, which its proof already supports: both `toCoeffField` values
reduce definitionally to `x ↦ a_L(x) − (k_L − k_m)_{□_m}`. -/
theorem fluxCorrectedCoeffFamily_aeEq_subConstFluxFamily (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (subConstFluxFamily M L m omega) := by
  intro Q
  refine Filter.Eventually.of_forall fun x => ?_
  show (Support.fluxCorrectedRegField M L m (originCube d m) omega).toFun x = _
  rw [Support.fluxCorrectedRegField_toFun]
  rfl

/-! ## The transported tower -/

/-- Together with the proved primal/adjoint split
`Annular.normalizedBlockResponseMax_isotropicComparator_le` this is what lets
Step 3's `J`-display bound the Step-1 endpoint's per-cube object. -/
theorem normalizedBlockResponseMax_fluxCorrected_eq [NeZero d] (M : ABKModel d)
    (L m : ℤ) (omega : Cutoff.CutoffSample d) (R : TriadicCube d) (a0 : Mat d) :
    Ch02.normalizedBlockResponseMax R
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega) a0 =
      Ch02.normalizedBlockResponseMax R (subConstFluxFamily M L m omega) a0 :=
  Ch02.normalizedBlockResponseMax_eq_ofAEEq
    (fluxCorrectedCoeffFamily_aeEq_subConstFluxFamily M L m omega) R a0

/-- The descendant-maximum level of the same identification. -/
theorem maxDescendantNormalizedBlockResponseAtScale_fluxCorrected_eq [NeZero d]
    (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (k : ℤ) (a0 : Mat d) :
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q k
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega) a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q k
        (subConstFluxFamily M L m omega) a0 :=
  Ch02.maxDescendantNormalizedBlockResponseAtScale_eq_ofAEEq
    (fluxCorrectedCoeffFamily_aeEq_subConstFluxFamily M L m omega) Q k a0

/-- **The endpoint's inner average, at Step 3's family.**  This is the exact
integrand shape of `Step1ScaleSum.step1_scaleSum_endpoint_originCube` and of
`Step2VolumeConversion.step2_volume_pointwise_originCube`. -/
theorem finsetAverage_rpow_normalizedBlockResponseMax_fluxCorrected_eq [NeZero d]
    (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
    (t : Finset (TriadicCube d)) (a0 : Mat d) (P : ℝ) :
    Ch02.finsetAverageReal t (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega) a0) P) =
      Ch02.finsetAverageReal t (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R
        (subConstFluxFamily M L m omega) a0) P) :=
  congrArg (Ch02.finsetAverageReal t)
    (funext fun R => congrArg (fun x => Real.rpow x P)
      (normalizedBlockResponseMax_fluxCorrected_eq M L m omega R a0))

/-- The two-argument `𝓔`-level identification: the object the a.e.-fidelity
certificate of `TwoScaleFidelity.lean` names may itself be read at Step 3's
family. -/
theorem homogenizationError_fluxCorrected_eq [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) (n : ℤ) (s : ℝ)
    (P R : Ch02.MultiscaleExponent) (a0 : Mat d) :
    Ch02.HomogenizationError Q n s P R
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega) a0 =
      Ch02.HomogenizationError Q n s P R (subConstFluxFamily M L m omega) a0 :=
  Ch02.HomogenizationError_eq_ofAEEq
    (fluxCorrectedCoeffFamily_aeEq_subConstFluxFamily M L m omega) Q n s P R a0

end

end Algsuperdiff.Section4.Provider.BoundsEaL
