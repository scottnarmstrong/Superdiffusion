/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Support.FluxCorrectedTwoScale

/-!
# The two-argument a.e.-fidelity certificate of the flux-corrected error

Nothing here imports that file, and nothing here claims the anchor.

## What this file discharges

`Algsuperdiff/Section4/Support/FluxCorrectedTwoScale.lean` proves the
two-argument `(m, n)` carrier of the anchor — the functional, the measurable
representative and the public `sup_{L ≥ m}` observable — and records, in its
module docstring, a **named provider obligation**: the a.e. identification of
that carrier with CoarseGraining's literal two-argument
`Ch02.HomogenizationError` at the flux-corrected coefficient family.  This file
discharges exactly that obligation, at a free truncation index `n ≤ m`.

The proved matched-index instance is
`Support.fluxCorrectedError_ae_eq_representative` (`n = m`, routed through
`Support.fluxCorrectedError_characterization`, whose right-hand side is
`Ch02.HomogenizationErrorOnCube`, i.e. `Ch02.HomogenizationError` with the
truncation index pinned to `Q.scale`).  Freeing the index costs nothing
mathematically:

* `Support.ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative`
  is stated for **every** triadic cube `R` on a single probability-one event, so
  it is already index-free;
* `Ch02.finsetSupReal_congr` transports that identity through the descendant
  maximum at the freed scale `n − l`;
* `Ch02.scaleResponseAtScale_infinity_rpow_two_eq` removes the square root of
  the `p = ∞` one-scale response at every scale `n − l ≤ m`, which is where the
  hypothesis `n ≤ m` (and only there) is used.

Consequently the whole content is the `Real.sqrt` / `Real.rpow (·) (1/2)`
spelling bridge plus a term-by-term `tsum_congr`.

## Main results

* `fluxCorrectedTwoScaleError_ae_eq_homogenizationError` — **the certificate.**
* `ae_forall_fluxCorrectedTwoScaleError_eq_homogenizationError` — the same
  identity for all `L ≥ m` on one probability-one event (the index set is
  countable).
* `fluxCorrectedTwoScaleErrorObservableSup_ae_eq_iSup_homogenizationError` —
  the certificate transported to the `[0,∞]`-valued observable that the frozen
  statement integrates.
* `fluxCorrectedError_ae_eq_homogenizationErrorOnCube` — the matched-index
  specialization, i.e. the consistency check against the proved one-argument
  chain.

## Binders

The only binders are the source binders (`M`, `L`, `m`, `n` with `n ≤ m`, the
positive `s`) and typing data: `[NeZero d]` is *forced by the target object* —
`Ch02.HomogenizationError` cannot be written without it — and is discharged
from any `M : ABKModel d` by the paper-wide `2 ≤ d` stored in
`M.shellPrefix.dimension` (the public
`Section3.Provider.Orlicz.neZero_of_model`, or any of its in-repo private
twins).  `NeZero` is a `Prop`-valued class, so the instance appearing here and
the one baked into `Support.fluxCorrectedTwoScaleErrorRepresentative` by its
`letI` are interchangeable definitionally; no bridge lemma is needed and none
is introduced.

## References

* ABK26, `d.mathcal.E`, (the two-argument definition and the `n := m`
  convention when the argument is dropped).
* ABK26, `l.bounds.mathcal.E.aL`, (the anchor whose left-hand side is the
  `sup_{L ≥ m}` observable identified here).
* `Algsuperdiff/Section4/Support/FluxCorrectedTwoScale.lean` (the carrier and
  the named obligation), `Support/FluxCorrectedRepresentative.lean` (the proved
  matched-index chain generalized here).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Algsuperdiff.Section3 Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Spelling bridges -/

/-- `Real.sqrt` in CoarseGraining's explicit `Real.rpow`-application spelling.
Mathlib states `Real.sqrt_eq_rpow` in the `HPow` notation, which `rw` does not
match against an application; this is a pure restatement (compare
`Section3.Provider.ErrorComparison.rpow_natCast'`). -/
theorem sqrt_eq_rpow_half (x : ℝ) : Real.sqrt x = Real.rpow x (1 / 2 : ℝ) :=
  Real.sqrt_eq_rpow x

/-- At `q = 2` the two-argument multiscale error is CoarseGraining's finite-`q`
branch. -/
theorem homogenizationError_finite_two_eq [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (P : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) :
    Ch02.HomogenizationError Q n s P (.finite 2) a a0 =
      Ch02.HomogenizationErrorFinite Q n s P 2 a a0 :=
  rfl

/-- The untruncated cube error is the two-argument error at the matched index. -/
theorem homogenizationErrorOnCube_eq_homogenizationError [NeZero d]
    (Q : TriadicCube d) (s : ℝ) (P R : Ch02.MultiscaleExponent)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    Ch02.HomogenizationErrorOnCube Q s P R a a0 =
      Ch02.HomogenizationError Q Q.scale s P R a a0 :=
  rfl

/-! ## The pointwise identity on the common event -/

/-- On the probability-one event of
`Support.ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative`,
the two-argument flux-corrected functional IS CoarseGraining's literal
two-argument `(∞, 2)` homogenization error at the flux-corrected family. -/
private theorem twoScaleFunctional_eq_homogenizationError_of_forall [NeZero d]
    (M : ABKModel d) (L m : ℤ) {n : ℤ} (hnm : n ≤ m) (s : ℝ)
    (omega : Cutoff.CutoffSample d)
    (hall : ∀ R : TriadicCube d,
      Ch02.normalizedBlockResponseMax R
          (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) =
        fluxCorrectedNormalizedBlockResponseRepresentative M L m (originCube d m) R
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega) :
    fluxCorrectedTwoScaleErrorFunctional M L m n s omega =
      Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2)
        (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  have hn : n ≤ (originCube d m).scale := hnm
  have hterm : ∀ l : ℕ,
      Ch02.geometricWeight s 2 l *
          Real.rpow (Ch02.scaleResponseAtScale (originCube d m) (n - (l : ℤ))
            .infinity (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M m))) 2 =
        Ch02.geometricWeight s 2 l *
          fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L m
            (originCube d m) (n - (l : ℤ))
            (isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega := by
    intro l
    have hk : n - (l : ℤ) ≤ (originCube d m).scale :=
      (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
    rw [Ch02.scaleResponseAtScale_infinity_rpow_two_eq (originCube d m) hk]
    exact congrArg (fun x => Ch02.geometricWeight s 2 l * x)
      (Ch02.finsetSupReal_congr _ fun R _ => hall R)
  have hE : Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2)
        (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M m)) =
      Real.rpow
        (∑' l : ℕ, Ch02.geometricWeight s 2 l *
          Real.rpow (Ch02.scaleResponseAtScale (originCube d m) (n - (l : ℤ))
            .infinity (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M m))) 2) (1 / 2) :=
    rfl
  rw [hE, tsum_congr hterm, ← sqrt_eq_rpow_half]
  rfl

/-! ## The certificate -/

/-- **The two-argument a.e.-fidelity certificate** (the named provider
obligation of `Support/FluxCorrectedTwoScale.lean`).

For every truncation index `n ≤ m`, the measurable two-argument representative
is almost surely CoarseGraining's literal two-argument `(∞, 2)` homogenization
error on the origin cube `□_m`, truncated at `n`, evaluated at the canonical
triadic family of the flux-corrected field `a_L − (k_L − k_m)_{□_m}` and at the
isotropic comparator `σ̄_m Id`. -/
theorem fluxCorrectedTwoScaleError_ae_eq_homogenizationError [NeZero d]
    (M : ABKModel d) (L m : ℤ) {n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      fluxCorrectedTwoScaleErrorRepresentative M L m n s omega =
        Ch02.HomogenizationError (originCube d m) n (s : ℝ) .infinity (.finite 2)
          (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  filter_upwards [ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative
    M L m (originCube d m) (isotropicComparatorMatrix (Annealed.sigmaBar M m))]
    with omega hall
  exact twoScaleFunctional_eq_homogenizationError_of_forall M L m hnm (s : ℝ) omega hall

/-- A single probability-one event carries the certificate for every `L ≥ m`,
because the index set is countable. -/
theorem ae_forall_fluxCorrectedTwoScaleError_eq_homogenizationError [NeZero d]
    (M : ABKModel d) (m : ℤ) {n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : {L : ℤ // m ≤ L},
        fluxCorrectedTwoScaleErrorRepresentative M L.1 m n s omega =
          Ch02.HomogenizationError (originCube d m) n (s : ℝ) .infinity (.finite 2)
            (fluxCorrectedCoeffFamily M L.1 m (originCube d m) omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M m)) :=
  MeasureTheory.ae_all_iff.2 fun L =>
    fluxCorrectedTwoScaleError_ae_eq_homogenizationError M L.1 m hnm s

/-- The certificate at the `[0,∞]`-valued observable of the frozen statement:
almost surely the two-argument observable supremum is the supremum of `ENNReal.ofReal` of
CoarseGraining's literal two-argument errors. -/
theorem fluxCorrectedTwoScaleErrorObservableSup_ae_eq_iSup_homogenizationError
    [NeZero d] (M : ABKModel d) (m : ℤ) {n : ℤ} (hnm : n ≤ m)
    (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      fluxCorrectedTwoScaleErrorObservableSup M m n s omega =
        ⨆ L : {L : ℤ // m ≤ L}, ENNReal.ofReal
          (Ch02.HomogenizationError (originCube d m) n (s : ℝ) .infinity (.finite 2)
            (fluxCorrectedCoeffFamily M L.1 m (originCube d m) omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M m))) := by
  filter_upwards [ae_forall_fluxCorrectedTwoScaleError_eq_homogenizationError
    M m hnm s] with omega hall
  exact iSup_congr fun L => congrArg ENNReal.ofReal (hall L)

/-! ## The matched-index consistency check -/

/-- At `n = m` the certificate is the proved one-argument identification: the
one-argument representative is a.s.  CoarseGraining's
`Ch02.HomogenizationErrorOnCube`.  This is the cross-check against
`Support.fluxCorrectedError_characterization` and
`Support.fluxCorrectedError_ae_eq_representative`, obtained here from the
freed-index certificate through the two `rfl` reductions
`Support.fluxCorrectedTwoScaleErrorRepresentative _ _ m m = _` and
`homogenizationErrorOnCube_eq_homogenizationError`. -/
theorem fluxCorrectedError_ae_eq_homogenizationErrorOnCube [NeZero d]
    (M : ABKModel d) (L m : ℤ) (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      fluxCorrectedErrorRepresentative M L m s omega =
        Ch02.HomogenizationErrorOnCube (originCube d m) (s : ℝ) .infinity (.finite 2)
          (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) :=
  fluxCorrectedTwoScaleError_ae_eq_homogenizationError M L m (le_refl m) s

end

end Algsuperdiff.Section4.Provider.BoundsEaL
