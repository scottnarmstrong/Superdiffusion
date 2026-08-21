/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.MajorantTransport

/-!
# The expectation transport at an almost sure majorant

## Why this module exists

`ExpectationTransport.lintegral_observableSup_rpow_le_tsum_lintegral_moment`
takes its `L`-uniform majorant hypothesis `hGmaj` at *every* sample.  That is
stronger than the anchor needs, and -- for the majorant produced here --
stronger than is true:

* the whole `L`-dependence of Step 3's display sits in the upper shell layers
  `k > m` (`ShellSlotBounds.lean`), so an `L`-free majorant exists exactly where
  the upper shell series converges;
* the sample carrier `Cutoff.CutoffSample` constrains only the lower tails
  (`Cutoff.LowerTailGood`, whose gauge is `localCubeControl` and whose
  direction is `m − r`, `r → ∞`); the layers above `m` are unconstrained
  coordinates of the product law.  Hence the series diverges on a null -- but
  nonempty -- set of shell sequences, and NO real-valued majorant can dominate
  the family for every sample.

Since the anchor's left-hand side is a `lintegral` of an `[0,∞]`-valued
observable, a null set costs nothing: an almost sure majorant suffices.

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

/-- `ENNReal.ofReal` of a nonnegative real `tsum` is at most the `ENNReal` `tsum`
of the terms, unconditionally. -/
private theorem ofReal_tsum_le_tsum_ofReal_of_nonneg {f : ℕ → ℝ} (hf : ∀ l, 0 ≤ f l) :
    ENNReal.ofReal (∑' l, f l) ≤ ∑' l, ENNReal.ofReal (f l) := by
  by_cases h : Summable f
  · exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg hf h)
  · rw [tsum_eq_zero_of_not_summable h, ENNReal.ofReal_zero]
    exact zero_le _

/-- A positive power commutes with suprema. -/
private theorem iSup_rpow_of_pos {ι : Sort*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, (f i) ^ p := by
  have h := (ENNReal.orderIsoRpow p hp).map_iSup f
  simp only [ENNReal.orderIsoRpow_apply] at h
  exact h

/-- A `finsetAverageReal` is monotone in its integrand on the averaging set. -/
private theorem finsetAverageReal_mono_on {α : Type*} (t : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ t, f x ≤ g x) :
    Ch02.finsetAverageReal t f ≤ Ch02.finsetAverageReal t g := by
  unfold Ch02.finsetAverageReal
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg) (by positivity)

/-! ## The transport -/

/-- Identical conclusion to
`ExpectationTransport.lintegral_observableSup_rpow_le_tsum_lintegral_moment`,
with `hGmaj` weakened from "for every sample" to "for almost every sample" --
the honest strength for a majorant built from the upper shell series. -/
theorem lintegral_observableSup_rpow_le_tsum_lintegral_moment_of_ae [NeZero d]
    (M : ABKModel d) {m n : ℤ} (hnm : n ≤ m) (s : {s : ℝ // 0 < s})
    (hs1 : (s : ℝ) ≤ 1) {p : ℝ} (hp : 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p)
    (G : ℕ → TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (hGmeas : ∀ l : ℕ, Measurable fun omega =>
      Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
        (fun R => Real.rpow (G l R omega) (p / 2)))
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
    rw [hom, iSup_rpow_of_pos _ hp0]
    refine iSup_le fun L => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg
      (homogenizationError_infinity_two_nonneg hnm hs0 _ _) hp0.le]
    refine le_trans (ENNReal.ofReal_le_ofReal
      (step2_volume_pointwise_originCube hnm
        (Support.fluxCorrectedCoeffFamily M L.1 m (originCube d m) omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) hs0 hs1 hp)) ?_
    rw [ENNReal.ofReal_mul hK]
    refine mul_le_mul_right (le_trans (ofReal_tsum_le_tsum_ofReal_of_nonneg (fun l => ?_)) ?_) _
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Section3.Provider.ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg
          (originCube d m) (n - (l : ℤ)) _ _ p)
    · refine ENNReal.tsum_le_tsum (fun l => ?_)
      have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      rw [ENNReal.ofReal_mul h3]
      refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
      refine finsetAverageReal_mono_on _ (fun R hR => ?_)
      exact Real.rpow_le_rpow (Ch02.normalizedBlockResponseMax_nonneg R _ _)
        (hmaj L.1 L.2 l R hR) (by linarith only [hp0])
  refine le_trans (lintegral_mono_ae hae) (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_tsum (fun l => (((hGmeas l).ennreal_ofReal).const_mul
      (ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ))))).aemeasurable)]
  refine congrArg (fun x => ENNReal.ofReal (Real.rpow (2 : ℝ) p *
      Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
      Ch02.geometricDiscount (s : ℝ) 1) * x) (tsum_congr fun l => ?_)
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## The composition at the `L`-free majorant -/

/-- **The anchor's left-hand side, at the `L`-free majorant, on an almost sure
tail gauge.**

The two remaining caller obligations are:

* `hTae` -- almost surely, the upper shell layer sums are bounded by `T`, at the
  sample AND at the negated sample (the second leg of the primal/adjoint split
  is read at `Nω`; the law-level invariance
  `Cutoff.map_negateCutoffSample_cutoffSampleLaw` is what makes the two legs cost
  the same, and is a caller's step, not used here);
* `hGmeas` -- the transport's measurability side condition at this majorant. -/
theorem lintegral_observableSup_rpow_le_tsum_lintegral_lFreeStep3Majorant_of_ae (d : ℕ)
    (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ), n ≤ m → ∀ (s : {s : ℝ // 0 < s}),
        (s : ℝ) ≤ 1 / 4 → M.gamma ≤ 1 / 8 →
        ∀ p : ℝ, 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p →
        ∀ T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ,
          (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            (∀ (k : ℤ) (v : Fin d → ℤ) (L : ℤ), m ≤ L →
              tailLayerSum m k v omega L ≤ T k v omega) ∧
            ∀ (k : ℤ) (v : Fin d → ℤ) (L : ℤ), m ≤ L →
              tailLayerSum m k v (Cutoff.negateCutoffSample omega) L ≤
                T k v (Cutoff.negateCutoffSample omega)) →
          (∀ l : ℕ, Measurable fun omega =>
            Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
              (fun R => Real.rpow
                (lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m T) (lFreeValueSlot m T) R
                  omega) (p / 2))) →
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
                        (lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m T)
                          (lFreeValueSlot m T) R omega) (p / 2)))
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hmaj⟩ :=
    exists_normalizedBlockResponseMax_le_lFreeStep3Majorant_of_tail d dimension
  refine ⟨C, hC, ?_⟩
  intro M m n hnm s hs1 hgam p hp T hTae hGmeas
  refine lintegral_observableSup_rpow_le_tsum_lintegral_moment_of_ae M hnm s
    (le_trans hs1 (by norm_num)) hp
    (fun _ R omega =>
      lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m T) (lFreeValueSlot m T) R omega)
    hGmeas ?_
  filter_upwards [hTae] with omega hT
  intro L hL l R hR
  exact hmaj M m n hnm (s : ℝ) s.2 hs1 hgam T omega hT.1 hT.2 L hL l R hR

end

end Algsuperdiff.Section4.Provider.BoundsEaL
