/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineResiduePairing

/-!
# `hlevel` and `hlevelDual` with the `EthmB(m)` pairing DISCHARGED

## What this file supplies

`HomSpineInstallPins.recutHlevel_of_residues` and its dual carry three
content-bearing hypotheses: the Theorem-C energy bound `hSbound`, and the pair
`hA`/`hB` together with the budget split `hsplit`.  This file DISCHARGES the
second group at the concrete substitution against the two summands of
`EthmB(m)`:

* the defect witness is cut at `E_B:= (EthmB(m))(ω).toReal` — the same cut
  `HomSpineFinalWitness` makes for the root's clause (C2);
* `C_w` is the explicit constant `recutPairCw`, the sum of the four pairing
  constants (two per level condition), none of which carries randomness;
* `hA`, `hB` are then `le_rfl` — the slots ARE the pairing's left-hand sides —
  and `hsplit` is `recutSplit_of_seam`.

What remains of the two level conditions is:

```text
  hSbound  (Theorem C's Step-2 energy density, at the printed constant shape)
  hdom1, hdom2  (the carrier seam — see `HomSpineResiduePairing`'s disclosure)
  hfin  (a.e. finiteness of the [0,∞] carrier: HomSpineFinalWitness's own step)
```

`recutPairCw` is bounded by the bundle's `K_abs` slot as a frame condition, not
proved here: `K_abs` is a free parameter of the endpoint.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The base order and the Step-2 random factor -/

/-- The printed base order `s = |log γ|⁻¹`, as a `FractionalOrder`.  Both
conditions come from `homS_le_quarter`, i.e. from `|log γ| ≥ 4`. -/
def recutOrderBase (M : ABKModel d) (hlog : 4 ≤ |Real.log M.gamma|) : FractionalOrder :=
  ⟨homS M, homS_pos (by linarith only [hlog]),
    lt_of_le_of_lt (homS_le_quarter hlog) (by norm_num)⟩

@[simp] theorem recutOrderBase_val (M : ABKModel d) (hlog : 4 ≤ |Real.log M.gamma|) :
    (recutOrderBase M hlog : FractionalOrder).1 = homS M := rfl

/-- **The random factor of the Step-2 constant**: the
minimal-scale factor `3^{(1-α)X_m(α)}` times the printed `1 + 𝓔_{1/4}(□_m)`,
cut to a real.  `hSbound`'s constant is `C_en = C · recutEnergyFactor`. -/
def recutEnergyFactor (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  (Y omega *
    (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal

theorem recutEnergyFactor_nonneg (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m : ℤ) (omega : Cutoff.CutoffSample d) : 0 ≤ recutEnergyFactor M Y m omega :=
  ENNReal.toReal_nonneg

/-! ## 2. The four pairing constants -/

/-- The two pairing constants of ONE level condition, added.  `κ` is the
condition's own multiplier (`1` for `hlevel`, the test-class constant for
`hlevelDual`) and `θ` its order ratio (`1`, respectively `7/8`). -/
def recutPairCwLeg (d : ℕ) (p : FiniteLpExponent) (s2 : FractionalOrder)
    (Cgap Cen0 sbase kappa theta : ℝ) : ℝ :=
  kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase +
    kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) * (s2.1 - theta * sbase)⁻¹ *
      cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap

/-- **THE BUNDLE'S `C_w`**: the four pairing constants of the two level
conditions.  Model-independent apart from `s = |log γ|⁻¹` and `γ⁵`'s constant. -/
def recutPairCw (d : ℕ) (p : FiniteLpExponent) (s2 : FractionalOrder)
    (Cgap Cen0 sbase Ktest : ℝ) : ℝ :=
  recutPairCwLeg d p s2 Cgap Cen0 sbase 1 1 +
    recutPairCwLeg d p s2 Cgap Cen0 sbase Ktest (7 / 8)

theorem recutPairCwLeg_nonneg (d : ℕ) (p : FiniteLpExponent) (s2 : FractionalOrder)
    {Cgap Cen0 sbase kappa theta : ℝ} (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hsbase : 0 < sbase) (hkappa : 0 ≤ kappa) (htheta : 0 < theta)
    (hwin : theta * sbase < s2.1) (hCdata0 : 0 ≤ cgOverlapDataConst d s2 p)
    (hs2gap : 5 < 10 * s2.1 * Real.log 3) :
    0 ≤ recutPairCwLeg d p s2 Cgap Cen0 sbase kappa theta := by
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcg d p := recutPinnedCcg_nonneg d p
  have hsig : (0 : ℝ) < theta * sbase := mul_pos htheta hsbase
  have hgapc : (0 : ℝ) ≤ homGapConstAt s2.1 := homGapConstAt_nonneg hs2gap
  have hthetapow : (0 : ℝ) ≤ theta ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg htheta.le _
  have hinv : (0 : ℝ) ≤ (s2.1 - theta * sbase)⁻¹ :=
    inv_nonneg.mpr (by linarith only [hwin])
  have h1 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hkappa hCcg0)
      (inv_nonneg.mpr hsig.le)) hCen0) hsbase.le
  have h2 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * homGapConstAt s2.1 / Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hkappa hCcg0) hthetapow) hinv) hCdata0) hgapc) hCgap.le
  rw [recutPairCwLeg]
  linarith only [h1, h2]

/-! ## 3. One level leg, paired against `EthmB(m)` -/

/-- **THE PAIRING OF ONE LEVEL CONDITION.**

The two slots of one level condition — at the order `θ·s` and with the
multiplier `κ` — are together below `EthmB(m)` times `recutPairCwLeg`.  The
first slot goes to `EthmB(m)`'s first summand, the second to its `γ⁵` summand
after `homGapAbsorbAt`.

The two `𝓔`-dominations `hdom1`, `hdom2` are the carrier seam disclosed in
`HomSpineResiduePairing`. -/
theorem recutLeg_ofReal_le [NeZero d] (M : ABKModel d) {Cgap : ℝ}
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
    {sbase kappa theta Cen0 E1 E2 : ℝ} (hs : 0 < homS M) (hsbase : sbase = homS M)
    (hlog : 4 ≤ |Real.log M.gamma|) (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap)
    (hkappa : 0 ≤ kappa) (htheta : 0 < theta) (hCen0 : 0 ≤ Cen0)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hCdata0 : 0 ≤ cgOverlapDataConst d s2 p)
    (hwin : theta * sbase < s2.1) (hs2gap : 5 < 10 * s2.1 * Real.log 3)
    (hdom1 : ENNReal.ofReal E1 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homHalf ⟨homS M, hs⟩) omega)
    (hdom2 : ENNReal.ofReal E2 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homQuarterOf ⟨homS M, hs⟩) omega) :
    ENNReal.ofReal
        (kappa *
            (recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
              (Cen0 * recutEnergyFactor M Y m omega)) +
          kappa *
            (recutPinnedCcg d p * (theta * sbase) ^ (-(9 / 2) : ℝ) *
                (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
                cgOverlapDataConst d s2 p *
              (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)))) ≤
      ENNReal.ofReal (recutPairCwLeg d p s2 Cgap Cen0 sbase kappa theta) *
        ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega := by
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
  /- the two pairing constan -/
  have hc1 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ :=
    mul_nonneg (mul_nonneg hkappa hCcg0) (inv_nonneg.mpr hsig.le)
  have hc2 : (0 : ℝ) ≤ kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
      (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hkappa hCcg0) hthetapow) hinvwin) hCdata0
  /- the two slots are nonnegati -/
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
    have h : (0 : ℝ) ≤ kappa * (recutPinnedCcg d p * (theta * sbase) ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ))) :=
      mul_nonneg hkappa (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg hCcg0 hsigpow) hinvwin) hE2sq) hCdata0) hthree)
    exact h
  /- the first l -/
  have hlegA : ENNReal.ofReal
      (kappa * (recutPinnedCcg d p * (theta * sbase)⁻¹ * E1 *
        (Cen0 * recutEnergyFactor M Y m omega))) ≤
      ENNReal.ofReal (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase) *
        ethmBFirst M Y m (homN M m) ⟨homS M, hs⟩ omega := by
    have hbase := ofReal_firstLeg_le M Y m (homN M m) ⟨homS M, hs⟩ omega
      (c := kappa * recutPinnedCcg d p * (theta * sbase)⁻¹) (Cen0 := Cen0) (E1 := E1)
      hc1 hCen0 hE1 hdom1
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
      _ ≤ ENNReal.ofReal (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * homS M) *
            ethmBFirst M Y m (homN M m) ⟨homS M, hs⟩ omega := hbase
      _ = ENNReal.ofReal (kappa * recutPinnedCcg d p * (theta * sbase)⁻¹ * Cen0 * sbase) *
            ethmBFirst M Y m (homN M m) ⟨homS M, hs⟩ omega := by rw [hsbase]
  /- the second l -/
  have hlegB : ENNReal.ofReal
      (kappa * (recutPinnedCcg d p * (theta * sbase) ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * (1 + E2 ^ (2 : ℕ)) * cgOverlapDataConst d s2 p *
        (3 : ℝ) ^ (s2.1 * (((homN M m : ℤ)) : ℝ) - s2.1 * (m : ℝ)))) ≤
      ENNReal.ofReal (kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
          (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p * homGapConstAt s2.1 /
          Cgap) *
        ethmBGap M Cgap m (homN M m) ⟨homS M, hs⟩ omega := by
    have hbase := ofReal_gapLeg_le M (Cgap := Cgap) m ⟨homS M, hs⟩ omega
      (c := kappa * recutPinnedCcg d p * theta ^ (-(9 / 2) : ℝ) *
        (s2.1 - theta * sbase)⁻¹ * cgOverlapDataConst d s2 p) (E2 := E2) (s2 := s2.1)
      hlog hgamma1 hCgap hc2 hE2 hs2gap hdom2
    refine le_trans (le_of_eq ?_) hbase
    have hsplitrpow : (theta * sbase) ^ (-(9 / 2) : ℝ) =
        theta ^ (-(9 / 2) : ℝ) * sbase ^ (-(9 / 2) : ℝ) := Real.mul_rpow htheta.le hsb.le
    rw [hsplitrpow, hsbase]
    congr 1
    ring
  /- add the two le -/
  rw [recutPairCwLeg]
  exact ofReal_add_le_ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega hA0 hB0
    (mul_nonneg (mul_nonneg hc1 hCen0) hsb.le)
    (div_nonneg (mul_nonneg hc2 hgapc) hCgap.le) hlegA hlegB

/-! ## 4. The bundle's `hsplit`, at `E_B = (EthmB(m))(ω).toReal` -/

/-- **THE BUDGET SPLIT.**  The real inequality the bundle's `hsplit` conjunct
is, at the explicit `C_w = recutPairCw` and the real cut of `EthmB(m)`. -/
theorem recutSplit_of_seam [NeZero d] (M : ABKModel d) {Cgap : ℝ}
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
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homHalf ⟨homS M, hs⟩) omega)
    (hdom2 : ENNReal.ofReal E2 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homQuarterOf ⟨homS M, hs⟩) omega)
    (hfin : ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ≠ ⊤) :
    A + B ≤ recutPairCw d p s2 Cgap Cen0 sbase Ktest *
      (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal := by
  have hsb : (0 : ℝ) < sbase := by rw [hsbase]; exact hs
  have hlegle := recutLeg_ofReal_le M Y m omega p s2 (sbase := sbase) (kappa := kappa)
    (theta := theta) (Cen0 := Cen0) (E1 := E1) (E2 := E2) hs hsbase hlog hgamma1 hCgap
    hkappa htheta hCen0 hE1 hE2 hCdata0 hwin hs2gap hdom1 hdom2
  have hCw0 : (0 : ℝ) ≤ recutPairCw d p s2 Cgap Cen0 sbase Ktest :=
    le_trans (recutPairCwLeg_nonneg d p s2 hCgap hCen0 hsb hkappa htheta hwin hCdata0
      hs2gap) hleg
  refine le_toReal_of_ofReal_le hCw0 hfin ?_
  refine le_trans (ENNReal.ofReal_le_ofReal (add_le_add hAle hBle)) ?_
  refine le_trans hlegle (mul_le_mul' (ENNReal.ofReal_le_ofReal hleg) le_rfl)

/-! ## 5. The two level conditions, with the pairing discharged -/

/-- **`hlevel`, from `hSbound` and the carrier seam alone.**

`HomSpineInstallPins.recutHlevel_of_residues` with `hA`, `hB` and `hsplit`
discharged: the two slots ARE the pairing's left-hand sides, `C_w` is the
explicit `recutPairCw`, and `E_B` is the real cut of `EthmB(m)`. -/
theorem recutHlevel_of_seam [NeZero d] (M : ABKModel d) (L : ℤ)
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
        (recutPinnedE1 M L omega m jn hsig (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homHalf ⟨homS M, hs⟩) omega)
    (hdom2 : ENNReal.ofReal
        (recutPinnedE2 M L omega m jn hsig (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homQuarterOf ⟨homS M, hs⟩) omega)
    (hfin : ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ≠ ⊤) :
    coarseGrainingFinitePRHS (recutPinnedCcg d p) (recutOrderBase M hlog).1 s2.1 sigmaBarM
        (recutPinnedE1 M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedE2 M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (recutPairCw d p s2 Cgap Cen0 (homS M) Ktest *
            (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
  obtain ⟨hlo, _hhi⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p := cgOverlapDataConst_nonneg d s2 p hlo
  have hE10 : (0 : ℝ) ≤ recutPinnedE1 M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE1_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hE20 : (0 : ℝ) ≤ recutPinnedE2 M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE2_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  refine recutHlevel_of_residues M L omega m jn hsig (recutOrderBase M hlog) p s2
    (Cen := Cen0 * recutEnergyFactor M Y m omega)
    (Cw := recutPairCw d p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal)
    hss2 hs2lt hs2gt hKg hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hSbound le_rfl le_rfl ?_
  refine recutSplit_of_seam M Y m omega p s2 (sbase := homS M) (kappa := 1) (theta := 1)
    (Cen0 := Cen0) (Ktest := Ktest) hs rfl hlog hgamma1 hCgap zero_le_one one_pos hCen0
    hE10 hE20 hCdata0 (by linarith only [hss2]) hs2gap ?_ ?_ ?_ hdom1 hdom2 hfin
  · rw [recutPairCw]
    have h2 := recutPairCwLeg_nonneg d p s2 (sbase := homS M) (kappa := Ktest)
      (theta := 7 / 8) hCgap hCen0 hs hKtest0 (by norm_num)
      (by linarith only [hss2, hs]) hCdata0 hs2gap
    linarith only [h2]
  · refine le_of_eq ?_
    simp only [recutOrderBase_val]
    ring
  · rw [hjn]
    refine le_of_eq ?_
    simp only [recutOrderBase_val, one_mul]

/-- **`hlevelDual`, from `hSbound` and the carrier seam alone.**

The same discharge at the dual order `7s/8`, with the test-class constant
`K_test` as the leg's multiplier.  The `C_w` and the `E_B` are the SAME as
`recutHlevel_of_seam`'s, so the two conditions fit one bundle. -/
theorem recutHlevelDual_of_seam [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d) (L : ℤ)
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
        (recutPinnedE1 M L omega m jn hsig (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m) (homHalf ⟨homS M, hs⟩) omega)
    (hdom2 : ENNReal.ofReal
        (recutPinnedE2 M L omega m jn hsig (recutOrderBase M hlog)) ≤
      fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
        (homQuarterOf ⟨homS M, hs⟩) omega)
    (hfin : ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ≠ ⊤) :
    cgTestConst d (originCube d m) (recutOrderBase M hlog).1
        (7 * (recutOrderBase M hlog).1 / 8) p.conjugate.exponent.toReal *
        (Real.rpow 3 (7 * (recutOrderBase M hlog).1 / 8 * (m : ℝ)) *
          coarseGrainingFinitePRHS (recutPinnedCcg d p)
            (7 * (recutOrderBase M hlog).1 / 8) s2.1 sigmaBarM
            (recutPinnedE1 M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedE2 M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ))) ≤
      Real.rpow 3 ((recutOrderBase M hlog).1 * (m : ℝ)) *
        (sigmaBarM *
          (recutPairCw d p s2 Cgap Cen0 (homS M) Ktest *
              (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) := by
  obtain ⟨hlo, _hhi⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p := cgOverlapDataConst_nonneg d s2 p hlo
  have hE10 : (0 : ℝ) ≤ recutPinnedE1 M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE1_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hE20 : (0 : ℝ) ≤ recutPinnedE2 M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE2_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hhalf : homS M / 2 ≤ 7 * homS M / 8 := by linarith only [hs]
  have hlts : 7 * homS M / 8 < homS M := by linarith only [hs]
  obtain ⟨hlodual, _hhidual⟩ := cgOrderWindow_of_guard (p := p) hd1 hs hguard hhalf hlts
  have hKtest0 : (0 : ℝ) ≤ Ktest := by
    rw [hKtest]; exact cgTestConstBase_nonneg d hlodual
  refine recutHlevelDual_of_residues hd1 M L omega m jn hsig (recutOrderBase M hlog) p s2
    (Cen := Cen0 * recutEnergyFactor M Y m omega)
    (Cw := recutPairCw d p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal)
    hguard (by simp only [recutOrderBase_val]; linarith only [hss2, hs]) hs2lt hs2gt
    hKg hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hSbound le_rfl le_rfl ?_
  refine recutSplit_of_seam M Y m omega p s2 (sbase := homS M) (kappa := Ktest)
    (theta := 7 / 8) (Cen0 := Cen0) (Ktest := Ktest) hs rfl hlog hgamma1 hCgap hKtest0
    (by norm_num) hCen0 hE10 hE20 hCdata0 (by linarith only [hss2, hs]) hs2gap ?_ ?_ ?_
    hdom1 hdom2 hfin
  · rw [recutPairCw]
    have h1 := recutPairCwLeg_nonneg d p s2 (sbase := homS M) (kappa := 1) (theta := 1)
      hCgap hCen0 hs zero_le_one one_pos (by linarith only [hss2]) hCdata0 hs2gap
    linarith only [h1]
  · refine le_of_eq ?_
    simp only [recutOrderBase_val]
    rw [← hKtest]
    ring
  · rw [hjn]
    refine le_of_eq ?_
    simp only [recutOrderBase_val]
    rw [← hKtest, show (7 * homS M / 8 : ℝ) = 7 / 8 * homS M from by ring]

end

end Algsuperdiff.Section4.Provider.Homogenization
