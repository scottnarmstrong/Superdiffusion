/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamRepin

/-!
# The level pairing at the re-pinned base `s/8`, absorbing the `√2`

## What moves

`HomSpineResidueLevel`'s pairing chain is stated at `EthmB(m)`'s PRINTED base
`⟨homS M, hs⟩` and takes both `𝓔`-dominations at constant one.  The re-pin
moves the base to `s' = s/8` (`HomSeamRepin.homSeamBase`) and delivers the
SECOND domination at `√2` (`seamDom2_of_bridge`-shaped), because the order step
`𝓔_{s/16,∞,2} ≤ √2 · 𝓔_{s/32,∞,2}` costs exactly the ratio of the two geometric
normalizations.  This file carries the two consequences:

* the gap pairing at a general domination constant `K ≥ 1`
  (`ofReal_gapLeg_le_of_const`), the constant entering as `K²` — the
  `ofReal_one_add_sq_le_of_const` is the whole of it;
* the level leg and the budget split at the re-pinned base and at `K = √2`
  (`recutSeamLeg_ofReal_le`, `recutSeamSplit_of_seam`), whose pairing constant
  is exactly `2 · recutPairCwLeg` resp. `2 · recutPairCw`.

The base re-pin is FREE on the first leg: `ofReal_firstLeg_le` returns the
constant `c · C_en0 · s'`, and `s' = s/8 ≤ s`, so the leg constant
already covers it.  The `√2` is the only genuine cost, and it is a factor `2`.

## Slot-agnosticism (and why the chain stops here)

Every theorem below takes the two error slots as BARE nonnegative reals `E1`,
`E2`.  It is therefore valid at the slots
(`HomSpineInstallPins.recutPinnedE1/E2`, at the uncut `a_L`) and equally at the
print-accurate slots (`HomSeamFluxCoefficient.recutPinnedE1Flux/E2Flux`, at
`ã_{L,m}`).  The chain deliberately stops before
`HomSpineResidueLevel.recutHlevel_of_seam`, which names `recutPinnedE1` and so
fixes the coefficient: see `HomSeamFluxCoefficient`'s module disclosure for why
the `a_L`-sided domination is not available and what the print-accurate
re-instantiation costs.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The gap pairing at a general domination constant -/

/-- The abstract shape of the gap pairing when the domination carries a
constant `K ≥ 1`: the constant enters squared, and nothing else changes. -/
private theorem ofReal_gapLeg_core_of_const {c gap Kg Cgap g5 E2 K : ℝ} (Ecar : ℝ≥0∞)
    (hc : 0 ≤ c) (hKg : 0 ≤ Kg) (hCgap : 0 < Cgap) (hg5 : 0 ≤ g5) (hE2 : 0 ≤ E2)
    (hK : 1 ≤ K) (hgap : gap ≤ Kg * g5)
    (hdom : ENNReal.ofReal E2 ≤ ENNReal.ofReal K * Ecar) :
    ENNReal.ofReal (c * gap * (1 + E2 ^ (2 : ℕ))) ≤
      ENNReal.ofReal (c * K ^ (2 : ℕ) * Kg / Cgap) *
        (ENNReal.ofReal (Cgap * g5) * (1 + Ecar ^ (2 : ℝ))) := by
  have hsq : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := pow_nonneg hE2 2
  have hone : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by linarith only [hsq]
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK]
  have hKsq : (0 : ℝ) ≤ K ^ (2 : ℕ) := pow_nonneg hK0 2
  have hstep : c * gap * (1 + E2 ^ (2 : ℕ)) ≤ c * (Kg * g5) * (1 + E2 ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hc) hone
  have hcK : (0 : ℝ) ≤ c * Kg / Cgap := div_nonneg (mul_nonneg hc hKg) hCgap.le
  have hCg5 : (0 : ℝ) ≤ Cgap * g5 := mul_nonneg hCgap.le hg5
  have hsplit : c * (Kg * g5) * (1 + E2 ^ (2 : ℕ)) =
      c * Kg / Cgap * (Cgap * g5) * (1 + E2 ^ (2 : ℕ)) := by
    field_simp
  have hprod : ENNReal.ofReal (c * Kg / Cgap * (Cgap * g5) * (1 + E2 ^ (2 : ℕ))) =
      ENNReal.ofReal (c * Kg / Cgap) *
        (ENNReal.ofReal (Cgap * g5) * ENNReal.ofReal (1 + E2 ^ (2 : ℕ))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hcK hCg5), ENNReal.ofReal_mul hcK, mul_assoc]
  have hconst : ENNReal.ofReal (c * Kg / Cgap) * ENNReal.ofReal (K ^ (2 : ℕ)) =
      ENNReal.ofReal (c * K ^ (2 : ℕ) * Kg / Cgap) := by
    rw [← ENNReal.ofReal_mul hcK]
    congr 1
    field_simp
  calc ENNReal.ofReal (c * gap * (1 + E2 ^ (2 : ℕ)))
      ≤ ENNReal.ofReal (c * (Kg * g5) * (1 + E2 ^ (2 : ℕ))) :=
        ENNReal.ofReal_le_ofReal hstep
    _ = ENNReal.ofReal (c * Kg / Cgap) *
          (ENNReal.ofReal (Cgap * g5) * ENNReal.ofReal (1 + E2 ^ (2 : ℕ))) := by
        rw [hsplit, hprod]
    _ ≤ ENNReal.ofReal (c * Kg / Cgap) *
          (ENNReal.ofReal (Cgap * g5) *
            (ENNReal.ofReal (K ^ (2 : ℕ)) * (1 + Ecar ^ (2 : ℝ)))) :=
        mul_le_mul' le_rfl
          (mul_le_mul' le_rfl (ofReal_one_add_sq_le_of_const hE2 hK hdom))
    _ = ENNReal.ofReal (c * K ^ (2 : ℕ) * Kg / Cgap) *
          (ENNReal.ofReal (Cgap * g5) * (1 + Ecar ^ (2 : ℝ))) := by
        rw [← hconst]; ring

/-- **THE SECOND PAIRING AT A GENERAL DOMINATION CONSTANT.**

`HomSpineResiduePairing.ofReal_gapLeg_le` with the domination weakened from
constant one to constant `K ≥ 1`.  The pairing constant picks up exactly `K²`;
the mesoscale gap absorption `homGapAbsorbAt` is untouched. -/
theorem ofReal_gapLeg_le_of_const (M : ABKModel d) {Cgap : ℝ} (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {c E2 s2 K : ℝ}
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hc : 0 ≤ c) (hE2 : 0 ≤ E2) (hs2 : 5 < 10 * s2 * Real.log 3) (hK : 1 ≤ K)
    (hdom : ENNReal.ofReal E2 ≤
      ENNReal.ofReal K *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homQuarterOf s) omega) :
    ENNReal.ofReal
        (c *
            (homS M ^ (-(9 / 2) : ℝ) *
              (3 : ℝ) ^ (s2 * (((homN M m : ℤ)) : ℝ) - s2 * (m : ℝ))) *
          (1 + E2 ^ (2 : ℕ))) ≤
      ENNReal.ofReal (c * K ^ (2 : ℕ) * homGapConstAt s2 / Cgap) *
        ethmBGap M Cgap m (homN M m) s omega := by
  have hgap := homGapAbsorbAt (M := M) hlog hgamma1 m hs2
  have hexp : (3 : ℝ) ^ (s2 * (((homN M m : ℤ)) : ℝ) - s2 * (m : ℝ)) =
      (3 : ℝ) ^ (s2 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) := by
    congr 1
    ring
  rw [hexp, ethmBGap]
  exact ofReal_gapLeg_core_of_const _ hc (homGapConstAt_nonneg hs2) hCgap
    (pow_nonneg M.shellPrefix.gamma_pos.le 5) hE2 hK hgap hdom

/-! ## 2. The level leg at the re-pinned base -/

/-- `(√2)² = 2`: the exact cost of the order step in the pairing constant. -/
theorem sqrtTwo_sq : (Real.sqrt 2) ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)

theorem one_le_sqrtTwo : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  simpa only [Real.sqrt_one] using h

/-- **THE PAIRING OF ONE LEVEL CONDITION, AT THE RE-PINNED BASE.**

`HomSpineResidueLevel.recutLeg_ofReal_le` with `EthmB(m)` instantiated at the
re-pinned base `s' = s/8` and the second domination taken at `√2`.  The pairing
constant is exactly `2 · recutPairCwLeg`: the first leg improves (its constant
is `c·C_en0·s'` with `s' = s/8 ≤ s`), the second costs the factor `(√2)² = 2`. -/
theorem recutSeamLeg_ofReal_le [NeZero d] (M : ABKModel d) {Cgap : ℝ}
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
    {sbase kappa theta Cen0 E1 E2 : ℝ} (hs : 0 < homS M) (hsbase : sbase = homS M)
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hkappa : 0 ≤ kappa) (htheta : 0 < theta) (hCen0 : 0 ≤ Cen0)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hCdata0 : 0 ≤ cgOverlapDataConst d s2 p)
    (hwin : theta * sbase < s2.1) (hs2gap : 5 < 10 * s2.1 * Real.log 3)
    (hdom1 : ENNReal.ofReal E1 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homHalf (homSeamBase M hs)) omega)
    (hdom2 : ENNReal.ofReal E2 ≤
      ENNReal.ofReal (Real.sqrt 2) *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homQuarterOf (homSeamBase M hs)) omega) :
    ENNReal.ofReal
        (kappa *
            (recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
              (Cen0 * recutEnergyFactor M Y m omega)) +
          kappa *
            (recutPinnedCcg d p * (theta * sbase) ^ (-(9 / 2) : ℝ) *
                (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
                cgOverlapDataConst d s2 p *
              (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)))) ≤
      ENNReal.ofReal (2 * recutPairCwLeg d p s2 Cgap Cen0 sbase kappa theta) *
        ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega := by
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcg d p := recutPinnedCcg_nonneg d p
  have hsb : (0 : ℝ) < sbase := by rw [hsbase]; exact hs
  have hsig : (0 : ℝ) < theta * sbase := mul_pos htheta hsb
  have hT0 : (0 : ℝ) ≤ recutEnergyFactor M Y m omega := recutEnergyFactor_nonneg M Y m omega
  have hthetapow : (0 : ℝ) ≤ theta ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg htheta.le _
  have hinvwin : (0 : ℝ) ≤ (s2.1 - theta * sbase)⁻¹ :=
    inv_nonneg.mpr (by linarith only [hwin])
  have hgapc : (0 : ℝ) ≤ homGapConstAt s2.1 := homGapConstAt_nonneg hs2gap
  have hthree : (0 : ℝ) ≤ (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hE2sq : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by
    have h := pow_nonneg hE2 2
    linarith only [h]
  have hc1 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ :=
    mul_nonneg (mul_nonneg hkappa hCcg0) (inv_nonneg.mpr hsig.le)
  have hc2 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hkappa hCcg0) hthetapow) hinvwin) hCdata0
  have hA0 : (0 : ℝ) ≤ kappa * (recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
      (Cen0 * recutEnergyFactor M Y m omega)) := by
    have h : (0 : ℝ) ≤ (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹) * E1 *
        (Cen0 * recutEnergyFactor M Y m omega) :=
      mul_nonneg (mul_nonneg hc1 hE1) (mul_nonneg hCen0 hT0)
    linarith only [h]
  have hB0 : (0 : ℝ) ≤ kappa * (recutPinnedCcg d p * (theta * sbase) ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
      (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ))) := by
    have hsigpow : (0 : ℝ) ≤ (theta * sbase) ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hsig.le _
    exact mul_nonneg hkappa (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hCcg0 hsigpow) hinvwin) hE2sq) hCdata0) hthree)
  /- the first leg, at the re-pinned ba -/
  have hlegA : ENNReal.ofReal
      (kappa * (recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
        (Cen0 * recutEnergyFactor M Y m omega))) ≤
      ENNReal.ofReal (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase) *
        ethmBFirst M Y m (homN M m) (homSeamBase M hs) omega := by
    have hbase := ofReal_firstLeg_le M Y m (homN M m) (homSeamBase M hs) omega
      (c := kappa * recutPinnedCcg d p * (theta * sbase)⁻¹) (Cen0 := Cen0) (E1 := E1)
      hc1 hCen0 hE1 hdom1
    have hshrink : kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 *
        ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ) ≤
        kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase := by
      have hcc : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 :=
        mul_nonneg hc1 hCen0
      have hle : ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ) ≤ sbase := by
        rw [homSeamBase_val, hsbase]; linarith only [hs]
      exact mul_le_mul_of_nonneg_left hle hcc
    calc ENNReal.ofReal (kappa * (recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
            (Cen0 * recutEnergyFactor M Y m omega)))
        = ENNReal.ofReal (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
            (Cen0 *
              (Y omega *
                (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter
                  omega)).toReal)) := by
          simp only [recutEnergyFactor]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 *
            ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ)) *
            ethmBFirst M Y m (homN M m) (homSeamBase M hs) omega := hbase
      _ ≤ ENNReal.ofReal (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase) *
            ethmBFirst M Y m (homN M m) (homSeamBase M hs) omega :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hshrink) le_rfl
  /- the second leg, at the re-pinned base and the √2 dominati -/
  have hlegB : ENNReal.ofReal
      (kappa * (recutPinnedCcg d p * (theta * sbase) ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)))) ≤
      ENNReal.ofReal (kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
          (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * 2 *
          homGapConstAt s2.1 / Cgap) *
        ethmBGap M Cgap m (homN M m) (homSeamBase M hs) omega := by
    have hbase := ofReal_gapLeg_le_of_const M (Cgap := Cgap) m (homSeamBase M hs) omega
      (c := kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p) (E2 := E2) (s2 := s2.1)
      (K := Real.sqrt 2) hlog hgamma1 hCgap hc2 hE2 hs2gap one_le_sqrtTwo hdom2
    rw [sqrtTwo_sq] at hbase
    refine le_trans (le_of_eq ?_) hbase
    have hsplitrpow : (theta * sbase) ^ (-(9 / 2) : ℝ) =
        theta ^ (-(9 / 2) : ℝ) * sbase ^ (-(9 / 2) : ℝ) := Real.mul_rpow htheta.le hsb.le
    rw [hsplitrpow, hsbase]
    congr 1
    ring
  /- add the two legs, then enlarge to `2 · recutPairCwLeg` -/
  have hcA0 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase :=
    mul_nonneg (mul_nonneg hc1 hCen0) hsb.le
  have hcB0 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * 2 *
      homGapConstAt s2.1 / Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg hc2 (by norm_num)) hgapc) hCgap.le
  have hsum : kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase +
      kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * 2 *
        homGapConstAt s2.1 / Cgap ≤
      2 * recutPairCwLeg d p s2 Cgap Cen0 sbase kappa theta := by
    rw [recutPairCwLeg]
    have h2 : kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * 2 *
        homGapConstAt s2.1 / Cgap =
        2 * (kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
          (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p *
          homGapConstAt s2.1 / Cgap) := by
      field_simp
    rw [h2]
    linarith only [hcA0]
  refine le_trans (ofReal_add_le_ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega
    hA0 hB0 hcA0 hcB0 hlegA hlegB) ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hsum) le_rfl

/-! ## 3. The budget split at the re-pinned base -/

/-- **THE BUDGET SPLIT, AT THE RE-PINNED BASE.**

`HomSpineResidueLevel.recutSplit_of_seam` with `EthmB(m)` at the base `s/8` and
the second domination at `√2`; the bundle's `C_w` is `2 · recutPairCw`. -/
theorem recutSeamSplit_of_seam [NeZero d] (M : ABKModel d) {Cgap : ℝ}
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
    {sbase kappa theta Cen0 E1 E2 Ktest A B : ℝ} (hs : 0 < homS M)
    (hsbase : sbase = homS M) (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1)
    (hCgap : 0 < Cgap) (hkappa : 0 ≤ kappa) (htheta : 0 < theta) (hCen0 : 0 ≤ Cen0)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hCdata0 : 0 ≤ cgOverlapDataConst d s2 p)
    (hwin : theta * sbase < s2.1) (hs2gap : 5 < 10 * s2.1 * Real.log 3)
    (hleg : recutPairCwLeg d p s2 Cgap Cen0 sbase kappa theta ≤
      recutPairCw d p s2 Cgap Cen0 sbase Ktest)
    (hAle : A ≤ kappa * (recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
      (Cen0 * recutEnergyFactor M Y m omega)))
    (hBle : B ≤ kappa * (recutPinnedCcg d p * (theta * sbase) ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
      (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ))))
    (hdom1 : ENNReal.ofReal E1 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homHalf (homSeamBase M hs)) omega)
    (hdom2 : ENNReal.ofReal E2 ≤
      ENNReal.ofReal (Real.sqrt 2) *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homQuarterOf (homSeamBase M hs)) omega)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤) :
    A + B ≤ 2 * recutPairCw d p s2 Cgap Cen0 sbase Ktest *
      (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal := by
  have hsb : (0 : ℝ) < sbase := by rw [hsbase]; exact hs
  have hlegle := recutSeamLeg_ofReal_le M Y m omega p s2 (sbase := sbase) (kappa := kappa)
    (theta := theta) (Cen0 := Cen0) (E1 := E1) (E2 := E2) hs hsbase hlog hgamma1 hCgap
    hkappa htheta hCen0 hE1 hE2 hCdata0 hwin hs2gap hdom1 hdom2
  have hCw0 : (0 : ℝ) ≤ recutPairCw d p s2 Cgap Cen0 sbase Ktest :=
    le_trans (recutPairCwLeg_nonneg d p s2 hCgap hCen0 hsb hkappa htheta hwin hCdata0
      hs2gap) hleg
  have hdouble : 2 * recutPairCwLeg d p s2 Cgap Cen0 sbase kappa theta ≤
      2 * recutPairCw d p s2 Cgap Cen0 sbase Ktest := by linarith only [hleg]
  refine le_toReal_of_ofReal_le (by linarith only [hCw0]) hfin ?_
  refine le_trans (ENNReal.ofReal_le_ofReal (add_le_add hAle hBle)) ?_
  exact le_trans hlegle (mul_le_mul' (ENNReal.ofReal_le_ofReal hdouble) le_rfl)

end

end Algsuperdiff.Section4.Provider.Homogenization
