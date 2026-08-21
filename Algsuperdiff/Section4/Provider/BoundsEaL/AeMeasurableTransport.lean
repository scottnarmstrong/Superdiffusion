/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.MajorantMeasurability

/-!
# The Step-2/Step-3 transport with BOTH side conditions discharged

## Why this module exists

`AeMajorantTransport.lintegral_observableSup_rpow_le_tsum_lintegral_moment_of_ae`
carries its measurability side condition `hGmeas` at `Measurable`.  The
transport's proof, however, uses `hGmeas` in exactly ONE place --
`MeasureTheory.lintegral_tsum` -- which asks only for `AEMeasurable`.

This module therefore re-derives that transport verbatim with `hGmeas` weakened
from `Measurable` to `AEMeasurable`, and then composes:

```
  TailSummability.ae_tailLayerSum_le_tailSeriesGauge          (hTae, discharged)
+ MajorantMeasurability.aemeasurable_finsetAverageReal_...    (hGmeas, discharged)
⟹  an UNCONDITIONAL bound for the anchor's Step-1/Step-2 left-hand side by the
    per-scale `tsum` of `lintegral`s of the L-FREE majorant.
```

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 2), (Step 3).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Three re-derived helpers -/

/-- `ENNReal.ofReal` of a nonnegative real `tsum` is at most the `tsum` of the terms,
unconditionally. -/
private theorem ofReal_tsum_le_tsum_ofReal_of_nonneg' {f : ℕ → ℝ} (hf : ∀ l, 0 ≤ f l) :
    ENNReal.ofReal (∑' l, f l) ≤ ∑' l, ENNReal.ofReal (f l) := by
  by_cases h : Summable f
  · exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg hf h)
  · rw [tsum_eq_zero_of_not_summable h, ENNReal.ofReal_zero]
    exact zero_le _

/-- A positive power commutes with suprema. -/
private theorem iSup_rpow_of_pos' {iota : Sort*} (f : iota → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, (f i) ^ p := by
  have h := (ENNReal.orderIsoRpow p hp).map_iSup f
  simp only [ENNReal.orderIsoRpow_apply] at h
  exact h

/-- A `finsetAverageReal` is monotone in its integrand on the averaging set. -/
private theorem finsetAverageReal_mono_on' {alpha : Type*} (t : Finset alpha)
    {f g : alpha → ℝ} (hfg : ∀ x ∈ t, f x ≤ g x) :
    Ch02.finsetAverageReal t f ≤ Ch02.finsetAverageReal t g := by
  unfold Ch02.finsetAverageReal
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg) (by positivity)

/-! ## The transport at an a.e. measurable majorant -/

/-- Identical conclusion to
`AeMajorantTransport.lintegral_observableSup_rpow_le_tsum_lintegral_moment_of_ae`,
with `hGmeas` weakened from `Measurable` to `AEMeasurable` -- the honest strength for an
integrand built from the `(2,2)` homogenization error, and exactly what the
single consuming step (`MeasureTheory.lintegral_tsum`) requires. -/
theorem lintegral_observableSup_rpow_le_tsum_lintegral_moment_of_ae_aemeasurable [NeZero d]
    (M : ABKModel d) {m n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s})
    (hs1 : (s : ℝ) ≤ 1) {p : ℝ} (hp : 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p)
    (G : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (hGmeas : ∀ l : ℕ, AEMeasurable (fun omega =>
      Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
        (fun R => Real.rpow (G l R omega) (p / 2)))
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hGmaj : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : ℤ, m ≤ L → ∀ (l : ℕ) (R : TriadicCube d),
        R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
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
      M m hnm s, hGmaj] with omega hom hmaj
    rw [hom, iSup_rpow_of_pos' _ hp0]
    refine iSup_le fun L => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg
      (homogenizationError_infinity_two_nonneg hnm hs0 _ _) hp0.le]
    refine le_trans (ENNReal.ofReal_le_ofReal
      (step2_volume_pointwise_originCube hnm
        (Support.fluxCorrectedCoeffFamily M L.1 m (originCube d m) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hs0 hs1 hp)) ?_
    rw [ENNReal.ofReal_mul hK]
    refine mul_le_mul_right (le_trans (ofReal_tsum_le_tsum_ofReal_of_nonneg' (fun l => ?_)) ?_) _
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Section3.Provider.ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg
          (originCube d m) (n - (l : ℤ)) _ _ p)
    · refine ENNReal.tsum_le_tsum (fun l => ?_)
      have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      rw [ENNReal.ofReal_mul h3]
      refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
      refine finsetAverageReal_mono_on' _ (fun R hR => ?_)
      exact Real.rpow_le_rpow (Ch02.normalizedBlockResponseMax_nonneg R _ _)
        (hmaj L.1 L.2 l R hR) (by linarith only [hp0])
  refine le_trans (lintegral_mono_ae hae) (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_tsum (fun l => ((hGmeas l).ennreal_ofReal).const_mul
      (ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ)))))]
  refine congrArg (fun x => ENNReal.ofReal (Real.rpow (2 : ℝ) p *
      Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
      Ch02.geometricDiscount (s : ℝ) 1) * x) (tsum_congr fun l => ?_)
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## The composed, binder-free transport -/

/-- **The transport, unconditional.**

The anchor's Step-1/Step-2 left-hand side -- the `p`-th `lintegral` of the
two-argument `sup_{L ≥ m}` flux-corrected observable -- is bounded by an explicit
constant times the per-scale `tsum` of `lintegral`s of the descendant averages of
`lFreeStep3Majorant^{p/2}`, an integrand that does not mention the truncation
index `L`.

* `hTae` is `TailSummability.ae_tailLayerSum_le_tailSeriesGauge` at the canonical
  gauge `T = tailSeriesGauge m`;
* `hGmeas` is `MajorantMeasurability.aemeasurable_finsetAverageReal_rpow_lFreeStep3Majorant`,
  read against the a.e. measurable transport above.

The hypotheses left are the source's own parameter ranges (`n ≤ m`, `0 < s ≤ 1/4`,
`γ ≤ 1/8`, `p ≥ 2d/s`) plus the dimension. -/
theorem lintegral_observableSup_rpow_le_tsum_lintegral_lFreeStep3Majorant_unconditional
    (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ), n ≤ m → ∀ (s : {s : ℝ // 0 < s}),
        (s : ℝ) ≤ 1 / 4 → M.gamma ≤ 1 / 8 →
        ∀ p : ℝ, 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p →
          (∫⁻ omega, Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p
              ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
            ENNReal.ofReal (Real.rpow (2 : ℝ) p *
                Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
                Ch02.geometricDiscount (s : ℝ) 1) *
              ∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ))) *
                ∫⁻ omega, ENNReal.ofReal
                    (Ch02.finsetAverageReal
                      (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                      (fun R => Real.rpow
                        (lFreeStep3Majorant C M m (s : ℝ)
                          (lFreeGradSlot m (tailSeriesGauge m))
                          (lFreeValueSlot m (tailSeriesGauge m)) R omega) (p / 2)))
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hmaj⟩ :=
    exists_normalizedBlockResponseMax_le_lFreeStep3Majorant_of_tail d dimension
  refine ⟨C, hC, ?_⟩
  intro M m n hnm s hs1 hgam p hp
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hp0 : 0 < p :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd0) (inv_pos.mpr s.2)) hp
  refine lintegral_observableSup_rpow_le_tsum_lintegral_moment_of_ae_aemeasurable M hnm s
    (le_trans hs1 (by norm_num)) hp
    (fun _ R omega =>
      lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m (tailSeriesGauge m))
        (lFreeValueSlot m (tailSeriesGauge m)) R omega)
    (fun l => aemeasurable_finsetAverageReal_rpow_lFreeStep3Majorant M C m n s hgam hp0.le
      (tailSeriesGauge m) (fun k v => measurable_tailSeriesGauge m k v) l) ?_
  filter_upwards [ae_tailLayerSum_le_tailSeriesGauge M m] with omega hT
  intro L hL l R hR
  exact hmaj M m n hnm (s : ℝ) s.2 hs1 hgam (tailSeriesGauge m) omega hT.1 hT.2 L hL l R hR

end

end Algsuperdiff.Section4.Provider.BoundsEaL
