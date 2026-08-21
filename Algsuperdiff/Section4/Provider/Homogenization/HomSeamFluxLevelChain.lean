/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamSqrtTwoChain
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLane

/-!
# The level pairing with the `Ccg` slot FREED, and its `ã` instance

## Why the `Ccg` slot has to be freed

`HomSeamSqrtTwoChain`'s pairing chain is stated at the pinned constant
`HomSpineInstallPins.recutPinnedCcg d p = (cgDualBoundConst d p).toReal`, which
is the `Classical.choose` of the `a_L` lane's existential.  The print-accurate
lane produces its own constant
`HomSeamFluxLane.cgDualBoundConstFlux d p`, and `Classical.choose` does not
reduce, so the two names are different reals even though they arise from the
SAME source constant `C(p,d)` of
`HomCGDischargeInstantiation.exists_printedCoarseGraining_of_dirichletPair`.

Section 1 therefore restates the pairing constants and the two pairing theorems
with `Ccg` a bare nonnegative real.  Nothing in the mathematics changes: the
proofs use the pinned constant only through its nonnegativity.  At `Ccg:=
recutPinnedCcg d p` these are exactly `HomSeamSqrtTwoChain`'s
`recutSeamLeg_ofReal_le` / `recutSeamSplit_of_seam`.

Section 2 instantiates at `Ccg:= recutPinnedCcgFlux d p` and at the
print-accurate error slots `recutPinnedE1Flux`/`recutPinnedE2Flux`, producing
the two level conditions of the re-cut bundle at

```text
  the coefficient  ã_{L,m},   the EthmB base  s' = s/8,   C_w = 2·pairCwOf.
```

## Scope

Nothing here is a source-facing claim.  The two level conditions are conditional
APIs whose remaining hypotheses are exactly `hSbound` (the Theorem-C Step-2
datum), the two `ã` dominations of `HomSeamFluxCoefficient`, and the a.e.
finiteness of the `[0,∞]` carrier.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The pairing constants and the two legs at a FREE `Ccg` -/

/-- `HomSpineResidueLevel.recutPairCwLeg` with the coarse-graining constant
freed.  At `Ccg:= recutPinnedCcg d p` this is that definition. -/
def pairCwLegOf (d : ℕ) (Ccg : ℝ) (p : FiniteLpExponent) (s2 : FractionalOrder)
    (Cgap Cen0 sbase kappa theta : ℝ) : ℝ :=
  kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase +
    kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
      cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap

/-- `HomSpineResidueLevel.recutPairCw` with the coarse-graining constant
freed. -/
def pairCwOf (d : ℕ) (Ccg : ℝ) (p : FiniteLpExponent) (s2 : FractionalOrder)
    (Cgap Cen0 sbase Ktest : ℝ) : ℝ :=
  pairCwLegOf d Ccg p s2 Cgap Cen0 sbase 1 1 +
    pairCwLegOf d Ccg p s2 Cgap Cen0 sbase Ktest (7 / 8)

theorem pairCwLegOf_nonneg (d : ℕ) {Ccg : ℝ} (p : FiniteLpExponent)
    (s2 : FractionalOrder) {Cgap Cen0 sbase kappa theta : ℝ} (hCcg0 : 0 ≤ Ccg)
    (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) (hsbase : 0 < sbase) (hkappa : 0 ≤ kappa)
    (htheta : 0 < theta) (hwin : theta * sbase < s2.1)
    (hCdata0 : 0 ≤ cgOverlapDataConst d s2 p) (hs2gap : 5 < 10 * s2.1 * Real.log 3) :
    0 ≤ pairCwLegOf d Ccg p s2 Cgap Cen0 sbase kappa theta := by
  have hsig : (0 : ℝ) < theta * sbase := mul_pos htheta hsbase
  have hgapc : (0 : ℝ) ≤ homGapConstAt s2.1 := homGapConstAt_nonneg hs2gap
  have hthetapow : (0 : ℝ) ≤ theta ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg htheta.le _
  have hinv : (0 : ℝ) ≤ (s2.1 - theta * sbase)⁻¹ :=
    inv_nonneg.mpr (by linarith only [hwin])
  have h1 : (0 : ℝ) ≤ kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hkappa hCcg0)
      (inv_nonneg.mpr hsig.le)) hCen0) hsbase.le
  have h2 : (0 : ℝ) ≤ kappa * Ccg * theta ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hkappa hCcg0) hthetapow) hinv) hCdata0) hgapc) hCgap.le
  rw [pairCwLegOf]
  linarith only [h1, h2]

/-- **THE PAIRING OF ONE LEVEL CONDITION, AT A FREE `Ccg` AND THE RE-PINNED
BASE.**

`HomSeamSqrtTwoChain.recutSeamLeg_ofReal_le` with the coarse-graining constant
freed; the proof is unchanged; it uses the pinned constant only through
its nonnegativity. -/
theorem seamLegOf_ofReal_le [NeZero d] (M : ABKModel d) {Cgap : ℝ}
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
    {Ccg sbase kappa theta Cen0 E1 E2 : ℝ} (hCcg0 : 0 ≤ Ccg) (hs : 0 < homS M)
    (hsbase : sbase = homS M) (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1)
    (hCgap : 0 < Cgap) (hkappa : 0 ≤ kappa) (htheta : 0 < theta) (hCen0 : 0 ≤ Cen0)
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
        (kappa * (Ccg * (theta * sbase)⁻¹ * E1 * (Cen0 * recutEnergyFactor M Y m omega)) +
          kappa *
            (Ccg * (theta * sbase) ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
                (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
              (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)))) ≤
      ENNReal.ofReal (2 * pairCwLegOf d Ccg p s2 Cgap Cen0 sbase kappa theta) *
        ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega := by
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
  have hc1 : (0 : ℝ) ≤ kappa * Ccg * (theta * sbase)⁻¹ :=
    mul_nonneg (mul_nonneg hkappa hCcg0) (inv_nonneg.mpr hsig.le)
  have hc2 : (0 : ℝ) ≤ kappa * Ccg * theta ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hkappa hCcg0) hthetapow) hinvwin) hCdata0
  have hA0 : (0 : ℝ) ≤ kappa * (Ccg * (theta * sbase)⁻¹ * E1 *
      (Cen0 * recutEnergyFactor M Y m omega)) := by
    have h : (0 : ℝ) ≤ (kappa * Ccg * (theta * sbase)⁻¹) * E1 *
        (Cen0 * recutEnergyFactor M Y m omega) :=
      mul_nonneg (mul_nonneg hc1 hE1) (mul_nonneg hCen0 hT0)
    linarith only [h]
  have hB0 : (0 : ℝ) ≤ kappa * (Ccg * (theta * sbase) ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
      (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ))) := by
    have hsigpow : (0 : ℝ) ≤ (theta * sbase) ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hsig.le _
    exact mul_nonneg hkappa (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hCcg0 hsigpow) hinvwin) hE2sq) hCdata0) hthree)
  /- the first leg, at the re-pinned ba -/
  have hlegA : ENNReal.ofReal
      (kappa * (Ccg * (theta * sbase)⁻¹ * E1 * (Cen0 * recutEnergyFactor M Y m omega))) ≤
      ENNReal.ofReal (kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase) *
        ethmBFirst M Y m (homN M m) (homSeamBase M hs) omega := by
    have hbase := ofReal_firstLeg_le M Y m (homN M m) (homSeamBase M hs) omega
      (c := kappa * Ccg * (theta * sbase)⁻¹) (Cen0 := Cen0) (E1 := E1)
      hc1 hCen0 hE1 hdom1
    have hshrink : kappa * Ccg * (theta * sbase)⁻¹ * Cen0 *
        ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ) ≤
        kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase := by
      have hcc : (0 : ℝ) ≤ kappa * Ccg * (theta * sbase)⁻¹ * Cen0 := mul_nonneg hc1 hCen0
      have hle : ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ) ≤ sbase := by
        rw [homSeamBase_val, hsbase]; linarith only [hs]
      exact mul_le_mul_of_nonneg_left hle hcc
    calc ENNReal.ofReal (kappa * (Ccg * (theta * sbase)⁻¹ * E1 *
            (Cen0 * recutEnergyFactor M Y m omega)))
        = ENNReal.ofReal (kappa * Ccg * (theta * sbase)⁻¹ * E1 *
            (Cen0 *
              (Y omega *
                (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter
                  omega)).toReal)) := by
          simp only [recutEnergyFactor]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (kappa * Ccg * (theta * sbase)⁻¹ * Cen0 *
            ((homSeamBase M hs : {s : ℝ // 0 < s}) : ℝ)) *
            ethmBFirst M Y m (homN M m) (homSeamBase M hs) omega := hbase
      _ ≤ ENNReal.ofReal (kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase) *
            ethmBFirst M Y m (homN M m) (homSeamBase M hs) omega :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hshrink) le_rfl
  /- the second leg, at the re-pinned base and the √2 dominati -/
  have hlegB : ENNReal.ofReal
      (kappa * (Ccg * (theta * sbase) ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
        (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)))) ≤
      ENNReal.ofReal (kappa * Ccg * theta ^ (-(9 / 2) : ℝ) *
          (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * 2 *
          homGapConstAt s2.1 / Cgap) *
        ethmBGap M Cgap m (homN M m) (homSeamBase M hs) omega := by
    have hbase := ofReal_gapLeg_le_of_const M (Cgap := Cgap) m (homSeamBase M hs) omega
      (c := kappa * Ccg * theta ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p) (E2 := E2) (s2 := s2.1)
      (K := Real.sqrt 2) hlog hgamma1 hCgap hc2 hE2 hs2gap one_le_sqrtTwo hdom2
    rw [sqrtTwo_sq] at hbase
    refine le_trans (le_of_eq ?_) hbase
    have hsplitrpow : (theta * sbase) ^ (-(9 / 2) : ℝ) =
        theta ^ (-(9 / 2) : ℝ) * sbase ^ (-(9 / 2) : ℝ) := Real.mul_rpow htheta.le hsb.le
    rw [hsplitrpow, hsbase]
    congr 1
    ring
  /- add the two legs, then enlarge to `2 · pairCwLegOf` -/
  have hcA0 : (0 : ℝ) ≤ kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase :=
    mul_nonneg (mul_nonneg hc1 hCen0) hsb.le
  have hcB0 : (0 : ℝ) ≤ kappa * Ccg * theta ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * 2 *
      homGapConstAt s2.1 / Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg hc2 (by norm_num)) hgapc) hCgap.le
  have hsum : kappa * Ccg * (theta * sbase)⁻¹ * Cen0 * sbase +
      kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
        cgOverlapDataConst d s2 p * 2 * homGapConstAt s2.1 / Cgap ≤
      2 * pairCwLegOf d Ccg p s2 Cgap Cen0 sbase kappa theta := by
    rw [pairCwLegOf]
    have h2 : kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
        cgOverlapDataConst d s2 p * 2 * homGapConstAt s2.1 / Cgap =
        2 * (kappa * Ccg * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
          cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap) := by
      field_simp
    rw [h2]
    linarith only [hcA0]
  refine le_trans (ofReal_add_le_ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega
    hA0 hB0 hcA0 hcB0 hlegA hlegB) ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hsum) le_rfl

/-- **THE BUDGET SPLIT, AT A FREE `Ccg` AND THE RE-PINNED BASE.**

`HomSeamSqrtTwoChain.recutSeamSplit_of_seam` with the coarse-graining constant
freed. -/
theorem seamSplitOf_of_seam [NeZero d] (M : ABKModel d) {Cgap : ℝ}
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
    {Ccg sbase kappa theta Cen0 E1 E2 Ktest A B : ℝ} (hCcg0 : 0 ≤ Ccg)
    (hs : 0 < homS M) (hsbase : sbase = homS M) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap) (hkappa : 0 ≤ kappa) (htheta : 0 < theta)
    (hCen0 : 0 ≤ Cen0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hCdata0 : 0 ≤ cgOverlapDataConst d s2 p)
    (hwin : theta * sbase < s2.1) (hs2gap : 5 < 10 * s2.1 * Real.log 3)
    (hleg : pairCwLegOf d Ccg p s2 Cgap Cen0 sbase kappa theta ≤
      pairCwOf d Ccg p s2 Cgap Cen0 sbase Ktest)
    (hAle : A ≤ kappa * (Ccg * (theta * sbase)⁻¹ * E1 *
      (Cen0 * recutEnergyFactor M Y m omega)))
    (hBle : B ≤ kappa * (Ccg * (theta * sbase) ^ (-(9 / 2) : ℝ) *
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
    A + B ≤ 2 * pairCwOf d Ccg p s2 Cgap Cen0 sbase Ktest *
      (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal := by
  have hsb : (0 : ℝ) < sbase := by rw [hsbase]; exact hs
  have hlegle := seamLegOf_ofReal_le M Y m omega p s2 (Ccg := Ccg) (sbase := sbase)
    (kappa := kappa) (theta := theta) (Cen0 := Cen0) (E1 := E1) (E2 := E2) hCcg0 hs
    hsbase hlog hgamma1 hCgap hkappa htheta hCen0 hE1 hE2 hCdata0 hwin hs2gap hdom1 hdom2
  have hCw0 : (0 : ℝ) ≤ pairCwOf d Ccg p s2 Cgap Cen0 sbase Ktest :=
    le_trans (pairCwLegOf_nonneg d p s2 hCcg0 hCgap hCen0 hsb hkappa htheta hwin hCdata0
      hs2gap) hleg
  have hdouble : 2 * pairCwLegOf d Ccg p s2 Cgap Cen0 sbase kappa theta ≤
      2 * pairCwOf d Ccg p s2 Cgap Cen0 sbase Ktest := by linarith only [hleg]
  refine le_toReal_of_ofReal_le (by linarith only [hCw0]) hfin ?_
  refine le_trans (ENNReal.ofReal_le_ofReal (add_le_add hAle hBle)) ?_
  exact le_trans hlegle (mul_le_mul' (ENNReal.ofReal_le_ofReal hdouble) le_rfl)

/-! ## 2. The `ã` pin of the `Ccg` slot -/

/-- The `Ccg` slot of the print-accurate lane, pinned to its own produced
constant. -/
def recutPinnedCcgFlux (d : ℕ) (p : FiniteLpExponent) : ℝ :=
  (cgDualBoundConstFlux d p).toReal

theorem recutPinnedCcgFlux_nonneg (d : ℕ) (p : FiniteLpExponent) :
    0 ≤ recutPinnedCcgFlux d p := ENNReal.toReal_nonneg

/-! ## 3. The two level conditions at `ã` and the re-pinned base -/

/-- **`hlevel` AT `ã_{L,m}` AND THE RE-PINNED BASE `s/8`.**

`HomSpineResidueLevel.recutHlevel_of_seam` with the coefficient moved to the
printed flux-corrected field, the `EthmB(m)` base moved to `s' = s/8`, and the
second domination taken at `√2`.  The remaining content-bearing hypotheses are
exactly `hSbound` and the two `ã` dominations. -/
theorem recutHlevelFlux_of_seam [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (p : FiniteLpExponent) (s2 : FractionalOrder) {g : Vec d → Vec d}
    {Kg Kh KhInf S Cen0 Ktest : ℝ} (hs : 0 < homS M)
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hss2 : homS M < s2.1) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hs2gap : 5 < 10 * s2.1 * Real.log 3) (hKtest0 : 0 ≤ Ktest)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh) (hCen0 : 0 ≤ Cen0)
    (hjn : (originCube d m).scale - (jn : ℤ) = homN M m)
    (hSbound : S ≤ Cen0 * recutEnergyFactor M Y m omega *
      energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hdom1 : ENNReal.ofReal
        (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homHalf (homSeamBase M hs)) omega)
    (hdom2 : ENNReal.ofReal
        (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog)) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homQuarterOf (homSeamBase M hs)) omega)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤) :
    coarseGrainingFinitePRHS (recutPinnedCcgFlux d p) (recutOrderBase M hlog).1 s2.1
        sigmaBarM (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (2 * pairCwOf d (recutPinnedCcgFlux d p) p s2 Cgap Cen0 (homS M) Ktest *
            (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo, _hhi⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p := cgOverlapDataConst_nonneg d s2 p hlo
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcgFlux d p := recutPinnedCcgFlux_nonneg d p
  have hE10 : (0 : ℝ) ≤ recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE1Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hE20 : (0 : ℝ) ≤ recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE2Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  refine hlevel_of_energyBound (Cdata := cgOverlapDataConst d s2 p)
    (Cen := Cen0 * recutEnergyFactor M Y m omega)
    (Cw := 2 * pairCwOf d (recutPinnedCcgFlux d p) p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal)
    hsig (recutOrderBase M hlog).2.1 (by simpa only [recutOrderBase_val] using hss2)
    hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hCdata0 hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) le_rfl le_rfl ?_
  refine seamSplitOf_of_seam M Y m omega p s2 (Ccg := recutPinnedCcgFlux d p)
    (sbase := homS M) (kappa := 1) (theta := 1) (Cen0 := Cen0) (Ktest := Ktest)
    hCcg0 hs rfl hlog hgamma1 hCgap zero_le_one one_pos hCen0 hE10 hE20 hCdata0
    (by linarith only [hss2]) hs2gap ?_ ?_ ?_ hdom1 hdom2 hfin
  · rw [pairCwOf]
    have h2 := pairCwLegOf_nonneg d p s2 (Ccg := recutPinnedCcgFlux d p)
      (sbase := homS M) (kappa := Ktest) (theta := 7 / 8) hCcg0 hCgap hCen0 hs hKtest0
      (by norm_num) (by linarith only [hss2, hs]) hCdata0 hs2gap
    linarith only [h2]
  · refine le_of_eq ?_
    simp only [recutOrderBase_val]
    ring
  · rw [hjn]
    refine le_of_eq ?_
    simp only [recutOrderBase_val, one_mul]
    rw [show (3 : ℝ) ^ (s2.1 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) =
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)) from by
      congr 1
      ring]

/-- **`hlevelDual` AT `ã_{L,m}` AND THE RE-PINNED BASE `s/8`.**

The same discharge at the dual order `7s/8`, with the test-class constant
`K_test` as the leg's multiplier.  The `C_w` and the `E_B` are the SAME as
`recutHlevelFlux_of_seam`'s, so the two conditions fit one bundle. -/
theorem recutHlevelDualFlux_of_seam [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (p : FiniteLpExponent) (s2 : FractionalOrder) {g : Vec d → Vec d}
    {Kg Kh KhInf S Cen0 Ktest : ℝ} (hs : 0 < homS M)
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hguard : homS M + (d : ℝ) / p.exponent.toReal ≤ 1 / 2)
    (hss2 : homS M < s2.1) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hs2gap : 5 < 10 * s2.1 * Real.log 3)
    (hKtest : Ktest =
      cgTestConstBase d (homS M) (7 * homS M / 8) p.conjugate.exponent.toReal)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh) (hCen0 : 0 ≤ Cen0)
    (hjn : (originCube d m).scale - (jn : ℤ) = homN M m)
    (hSbound : S ≤ Cen0 * recutEnergyFactor M Y m omega *
      energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hdom1 : ENNReal.ofReal
        (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homHalf (homSeamBase M hs)) omega)
    (hdom2 : ENNReal.ofReal
        (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog)) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
          (homQuarterOf (homSeamBase M hs)) omega)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤) :
    cgTestConst d (originCube d m) (recutOrderBase M hlog).1
        (7 * (recutOrderBase M hlog).1 / 8) p.conjugate.exponent.toReal *
        (Real.rpow 3 (7 * (recutOrderBase M hlog).1 / 8 * (m : ℝ)) *
          coarseGrainingFinitePRHS (recutPinnedCcgFlux d p)
            (7 * (recutOrderBase M hlog).1 / 8) s2.1 sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ))) ≤
      Real.rpow 3 ((recutOrderBase M hlog).1 * (m : ℝ)) *
        (sigmaBarM *
          (2 * pairCwOf d (recutPinnedCcgFlux d p) p s2 Cgap Cen0 (homS M) Ktest *
              (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo2, _hhi2⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p :=
    cgOverlapDataConst_nonneg d s2 p hlo2
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcgFlux d p := recutPinnedCcgFlux_nonneg d p
  have hE10 : (0 : ℝ) ≤ recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE1Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hE20 : (0 : ℝ) ≤ recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE2Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hhalf : homS M / 2 ≤ 7 * homS M / 8 := by linarith only [hs]
  have hlts : 7 * homS M / 8 < homS M := by linarith only [hs]
  obtain ⟨hlodual, _hhidual⟩ := cgOrderWindow_of_guard (p := p) hd1 hs hguard hhalf hlts
  have hKtest0 : (0 : ℝ) ≤ Ktest := by
    rw [hKtest]; exact cgTestConstBase_nonneg d hlodual
  refine hlevelDual_of_energyBound (Cdata := cgOverlapDataConst d s2 p)
    (Cen := Cen0 * recutEnergyFactor M Y m omega)
    (Cw := 2 * pairCwOf d (recutPinnedCcgFlux d p) p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal)
    hsig (by simp only [recutOrderBase_val]; linarith only [hs])
    (by simp only [recutOrderBase_val]; linarith only [hss2, hs])
    (by simpa only [recutOrderBase_val] using hlodual)
    hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hCdata0 hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) le_rfl le_rfl ?_
  refine seamSplitOf_of_seam M Y m omega p s2 (Ccg := recutPinnedCcgFlux d p)
    (sbase := homS M) (kappa := Ktest) (theta := 7 / 8) (Cen0 := Cen0) (Ktest := Ktest)
    hCcg0 hs rfl hlog hgamma1 hCgap hKtest0 (by norm_num) hCen0 hE10 hE20 hCdata0
    (by linarith only [hss2, hs]) hs2gap ?_ ?_ ?_ hdom1 hdom2 hfin
  · rw [pairCwOf]
    have h1 := pairCwLegOf_nonneg d p s2 (Ccg := recutPinnedCcgFlux d p)
      (sbase := homS M) (kappa := 1) (theta := 1) hCcg0 hCgap hCen0 hs zero_le_one one_pos
      (by linarith only [hss2]) hCdata0 hs2gap
    linarith only [h1]
  · refine le_of_eq ?_
    simp only [recutOrderBase_val]
    rw [← hKtest]
    ring
  · rw [hjn]
    refine le_of_eq ?_
    simp only [recutOrderBase_val]
    rw [← hKtest, show (7 * homS M / 8 : ℝ) = 7 / 8 * homS M from by ring,
      show (3 : ℝ) ^ (s2.1 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) =
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)) from by
      congr 1
      ring]

end

end Algsuperdiff.Section4.Provider.Homogenization
