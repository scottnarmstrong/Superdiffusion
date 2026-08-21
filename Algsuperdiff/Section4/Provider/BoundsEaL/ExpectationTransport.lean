/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.Step2VolumeConversion
import Algsuperdiff.Section4.Provider.BoundsEaL.TwoScaleFidelity

/-!
# The expectation transport: from the pointwise Step-1/2 chain to the `lintegral`

Nothing here imports that file, and nothing here claims the anchor.

## What this module does

Steps 1--2 (`Step1ScaleSum.lean`, `Step2VolumeConversion.lean`) end at a bound
that is *pointwise in the sample* and holds for each truncation index `L`:

```
𝓔_{s,∞,2}(□_m, n; ã_{L,m}(ω), σ̄_m Id)^p
  ≤ 2^p 3^{(1/2) p s (m−n)} 𝔠_s ∑_{l ≥ 0} 3^{−sl} ⨍_{R ∈ desc(□_m, n−l)} 𝔍(R; ω)^{p/2} ,
```

with `𝔍(R; ω) = Ch02.normalizedBlockResponseMax R (ã_{L,m}(ω)) (σ̄_m Id)`.  The
anchor integrates instead the `[0,∞]`-valued observable
`Support.fluxCorrectedTwoScaleErrorObservableSup`, i.e. the supremum over
`L ≥ m` of `ENNReal.ofReal` of the measurable representative.  This module performs the
transport:

3. `ENNReal.ofReal` monotonicity plus `lintegral_const_mul'` and `lintegral_tsum`
   exchange the integral with the scale sum and the constants.

## The `L`-uniformity hypothesis (an explicit conditional A obligation)

The majorant `G l R ω` is a *parameter* here, subject to the single hypothesis
`hGmaj`: it dominates the per-cube block response maximum of the carrier family
**for every `L ≥ m`**.  It is a caller-supplied mathematical obligation, not a
source premise.

## Main results

* `lintegral_observableSup_rpow_le_tsum_lintegral_moment` — the anchor's
  left-hand side bounded by an explicit constant times a `tsum` of per-scale
  `lintegral`s of the per-cube moment objects.
* `homogenizationError_infinity_two_nonneg` — the nonnegativity the `ofReal`
  bookkeeping needs, from CoarseGraining's descendant-maximum nonnegativity.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 2).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Three re-derived helpers -/

/-- `ENNReal.ofReal` of a nonnegative real `tsum` is at most the `tsum` of the terms --
unconditionally: if the family is not summable the left side is `ofReal 0 = 0`.
(Mathlib's `ENNReal.ofReal_tsum_of_nonneg` is the equality under a summability
hypothesis, which the abstract majorant below does not carry.) -/
private theorem ofReal_tsum_le_tsum_ofReal {f : ℕ → ℝ} (hf : ∀ l, 0 ≤ f l) :
    ENNReal.ofReal (∑' l, f l) ≤ ∑' l, ENNReal.ofReal (f l) := by
  by_cases h : Summable f
  · exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg hf h)
  · rw [tsum_eq_zero_of_not_summable h, ENNReal.ofReal_zero]
    exact zero_le _

/-- A positive power commutes with suprema, because it is an order isomorphism of
`[0,∞]`. -/
private theorem iSup_rpow {ι : Sort*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, (f i) ^ p := by
  have h := (ENNReal.orderIsoRpow p hp).map_iSup f
  simp only [ENNReal.orderIsoRpow_apply] at h
  exact h

/-- A `finsetAverageReal` is monotone in its integrand on the averaging set.
(Re-derivation of the `private` helper of
`Section3/Provider/Localization/Breakdown.lean`.) -/
private theorem finsetAverageReal_mono {α : Type*} (t : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ t, f x ≤ g x) :
    Ch02.finsetAverageReal t f ≤ Ch02.finsetAverageReal t g := by
  unfold Ch02.finsetAverageReal
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg) (by positivity)

/-! ## Nonnegativity of the integrand -/

/-- The two-argument `(∞, 2)` multiscale error is nonnegative: each of its scale
responses is an `rpow` of the descendant block-response maximum. -/
theorem homogenizationError_infinity_two_nonneg [NeZero d] {m n : ℤ} (hnm : n ≤ m)
    {s : ℝ} (hs : 0 < s) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2) F a0 := by
  refine homogenizationError_finite_q_nonneg (originCube d m) n hs
    (by norm_num : (0 : ℝ) < 2) .infinity F a0 (fun l => ?_)
  have hk : n - (l : ℤ) ≤ (originCube d m).scale :=
    (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hnm
  exact Real.rpow_nonneg
    (Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m) hk F a0) _

/-! ## The transport -/

/-- ```
ofReal (2^p 3^{(1/2) p s (m−n)} 𝔠_s) · ∑_{l ≥ 0} ofReal (3^{−sl}) ·
  ∫⁻ ω, ofReal ( ⨍_{R ∈ desc(□_m, n−l)} G(l, R, ω)^{p/2} ) .
```

Nothing about `p` beyond the source's own floor `p ≥ 2ds^{-1}` is used. -/
theorem lintegral_observableSup_rpow_le_tsum_lintegral_moment [NeZero d]
    (M : ABKModel d) {m n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s})
    (hs1 : (s : ℝ) ≤ 1) {p : ℝ} (hp : 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p)
    (G : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (hGmeas : ∀ l : ℕ, Measurable fun omega =>
      Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
        (fun R => Real.rpow (G l R omega) (p / 2)))
    (hGmaj : ∀ L : ℤ, m ≤ L → ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
      ∀ omega : Cutoff.CutoffSample d,
        Ch02.normalizedBlockResponseMax R
            (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
          G l R omega) :
    (∫⁻ omega, Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (Real.rpow (2 : ℝ) p *
          Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
          Ch02.geometricDiscount (s : ℝ) 1) *
        ∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ))) *
          ∫⁻ omega, ENNReal.ofReal
              (Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                (fun R => Real.rpow (G l R omega) (p / 2)))
            ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hp0 : 0 < p :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd0) (inv_pos.mpr hs0)) hp
  have hcs : (0 : ℝ) < Ch02.geometricDiscount (s : ℝ) 1 :=
    Homogenization.geometricDiscount_pos (s := (s : ℝ)) (q := (1 : ℝ)) (by linarith only [hs0])
  have hK : (0 : ℝ) ≤ Real.rpow (2 : ℝ) p *
      Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
      Ch02.geometricDiscount (s : ℝ) 1 :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by norm_num) _)) hcs.le
  -- the `L`-uniform pointwise bound, in `[0,∞]`
  have hterm : ∀ (L : ℤ) (omega : Cutoff.CutoffSample d), m ≤ L →
      ENNReal.ofReal (Ch02.HomogenizationError (originCube d m) n (s : ℝ) .infinity
          (.finite 2) (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) ^ p ≤
        ENNReal.ofReal (Real.rpow (2 : ℝ) p *
            Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
            Ch02.geometricDiscount (s : ℝ) 1) *
          ∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ))) *
            ENNReal.ofReal
              (Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                (fun R => Real.rpow (G l R omega) (p / 2))) := by
    intro L omega hL
    rw [ENNReal.ofReal_rpow_of_nonneg
      (homogenizationError_infinity_two_nonneg hnm hs0 _ _) hp0.le]
    refine le_trans (ENNReal.ofReal_le_ofReal
      (step2_volume_pointwise_originCube hnm
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hs0 hs1 hp)) ?_
    rw [ENNReal.ofReal_mul hK]
    refine mul_le_mul_right (le_trans (ofReal_tsum_le_tsum_ofReal (fun l => ?_)) ?_) _
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Section3.Provider.ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg
          (originCube d m) (n - (l : ℤ)) _ _ p)
    · refine ENNReal.tsum_le_tsum (fun l => ?_)
      have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      rw [ENNReal.ofReal_mul h3]
      refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
      refine finsetAverageReal_mono _ (fun R hR => ?_)
      exact Real.rpow_le_rpow (Ch02.normalizedBlockResponseMax_nonneg R _ _)
        (hGmaj L hL l R hR omega) (by linarith only [hp0])
  -- the observable, almost surely
  have hae : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p ≤
        ENNReal.ofReal (Real.rpow (2 : ℝ) p *
            Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
            Ch02.geometricDiscount (s : ℝ) 1) *
          ∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ))) *
            ENNReal.ofReal
              (Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                (fun R => Real.rpow (G l R omega) (p / 2))) := by
    filter_upwards [fluxCorrectedTwoScaleErrorObservableSup_ae_eq_iSup_homogenizationError
      M m hnm s] with omega hom
    rw [hom, iSup_rpow _ hp0]
    exact iSup_le fun L => hterm L.1 omega L.2
  -- integrate
  refine le_trans (lintegral_mono_ae hae) (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_tsum (fun l => (((hGmeas l).ennreal_ofReal).const_mul
      (ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ))))).aemeasurable)]
  refine congrArg (fun x => ENNReal.ofReal (Real.rpow (2 : ℝ) p *
      Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
      Ch02.geometricDiscount (s : ℝ) 1) * x) (tsum_congr fun l => ?_)
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end

end Algsuperdiff.Section4.Provider.BoundsEaL
