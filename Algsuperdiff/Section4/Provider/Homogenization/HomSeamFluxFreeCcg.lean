/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxCoreSupply

/-!
# The `ã` core and its supply with the `Ccg` slot FREED

## Why this file exists

`HomSeamFluxCoreSupply` states its core, its supply and its producer at the
PINNED coarse-graining constant `recutPinnedCcgFlux d p = (cgDualBoundConstFlux d
p).toReal`, while the two level lemmas it consumes
(`recutHlevelFlux_of_seam`, `recutHlevelDualFlux_of_seam`) are likewise pinned —
even though `HomSeamFluxLevelChain`'s own pairing chain (`seamSplitOf_of_seam`)
is already stated at a FREE `Ccg`.  A clause producer that delivers its own
constant `Ccg₀` therefore cannot enter the chain without a detour.

This file removes the detour: every statement below carries `Ccg` as a bare
real, constrained only by

```text
  0 ≤ Ccg                                  (the pairing chain's own use), and
  cgDualBoundConstFlux d p ≤ ofReal Ccg    (the bundle's own conjunct).
```

Both are monotone UP in `Ccg`, so a clause produced at any `Ccg₀` composes at
`max Ccg₀ (recutPinnedCcgFlux d p)`; at `Ccg = recutPinnedCcgFlux d p` the
statements are `HomSeamFluxCoreSupply`'s, with the second hypothesis discharged
by `cgDualBoundConstFlux_dominates_self`.

NOTHING mathematical changes.  The proofs use the pinned constant only through
its nonnegativity and through that one domination; both are hypotheses here.
In particular this file makes NO claim about which constant the multiscale
clause can actually be produced at.

## Disclosure

The pairing constant `recutCwFluxAt` is LINEAR in `Ccg` (both legs of
`pairCwOf` are), so a `Ccg` that grows with the model grows `C_w` — and hence
`K_abs` — by the same factor.  Freeing the slot does not make a model-dependent
`Ccg` free of charge; it only makes the entry point honest.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The pairing constant at a free `Ccg` -/

/-- `HomSeamFluxCoreSupply.recutPinnedCwFlux` with the coarse-graining constant
freed.  At `Ccg = recutPinnedCcgFlux d (recutExponent d hd1)` this is that
definition. -/
def recutCwFluxAt (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d) (Ccg Cgap Cen0 : ℝ) : ℝ :=
  2 * pairCwOf d Ccg (recutExponent d hd1) recutOrderTop Cgap Cen0 (homS M)
    (recutPinnedKtest d hd1 M)

theorem recutCwFluxAt_eq_pinned (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d) (Cgap Cen0 : ℝ) :
    recutCwFluxAt d hd1 M (recutPinnedCcgFlux d (recutExponent d hd1)) Cgap Cen0 =
      recutPinnedCwFlux d hd1 M Cgap Cen0 := rfl

/-- The pairing constant at a free `Ccg` is nonnegative. -/
theorem recutCwFluxAt_nonneg {d : ℕ} (hd1 : 1 ≤ d) (M : ABKModel d) {Ccg Cgap Cen0 : ℝ}
    (hCcg0 : 0 ≤ Ccg) (hs : 0 < homS M) (hlog : 4 ≤ |Real.log M.gamma|)
    (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) : 0 ≤ recutCwFluxAt d hd1 M Ccg Cgap Cen0 := by
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 :=
    recutExponent_quotient d hd1
  have hguard : homS M + (d : ℝ) / (recutExponent d hd1).exponent.toReal ≤ 1 / 2 := by
    rw [hquot]; linarith only [hquarter]
  have hss2 : homS M < (recutOrderTop : FractionalOrder).1 := by
    rw [recutOrderTop_val]; linarith only [hquarter]
  obtain ⟨hs2lt, hs2gt⟩ := recutOrderTop_window d hd1
  have hgapexp := recutOrderTop_gapExponent
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d recutOrderTop (recutExponent d hd1) :=
    cgOverlapDataConst_nonneg d recutOrderTop (recutExponent d hd1)
      (holderHalf_window (p := recutExponent d hd1) hs2lt hs2gt).1
  have hhalf : homS M / 2 ≤ 7 * homS M / 8 := by linarith only [hs]
  have hlts : 7 * homS M / 8 < homS M := by linarith only [hs]
  obtain ⟨hlodual, _hhidual⟩ :=
    cgOrderWindow_of_guard (p := recutExponent d hd1) hd1 hs hguard hhalf hlts
  have hKtest0 : (0 : ℝ) ≤ recutPinnedKtest d hd1 M := cgTestConstBase_nonneg d hlodual
  have h1 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop
    (Ccg := Ccg) (Cgap := Cgap) (Cen0 := Cen0)
    (sbase := homS M) (kappa := 1) (theta := 1) hCcg0 hCgap hCen0 hs zero_le_one one_pos
    (by linarith only [hss2]) hCdata0 hgapexp
  have h2 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop
    (Ccg := Ccg) (Cgap := Cgap) (Cen0 := Cen0)
    (sbase := homS M) (kappa := recutPinnedKtest d hd1 M) (theta := 7 / 8) hCcg0 hCgap
    hCen0 hs hKtest0 (by norm_num) (by linarith only [hss2, hs]) hCdata0 hgapexp
  rw [recutCwFluxAt, pairCwOf]
  linarith only [h1, h2]

/-! ## 2. The two level conditions at a free `Ccg` -/

/-- **`hlevel` AT A FREE `Ccg`, THE `ã` COEFFICIENT AND THE BASE `s/8`.**

`HomSeamFluxLevelChain.recutHlevelFlux_of_seam` with the coarse-graining
constant freed; the proof is unchanged; it uses the pinned constant only
through its nonnegativity. -/
theorem hlevelFluxAt_of_seam [NeZero d] (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (p : FiniteLpExponent) (s2 : FractionalOrder) {g : Vec d → Vec d}
    {Ccg Kg Kh KhInf S Cen0 Ktest : ℝ} (hCcg0 : 0 ≤ Ccg) (hs : 0 < homS M)
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
    coarseGrainingFinitePRHS Ccg (recutOrderBase M hlog).1 s2.1
        sigmaBarM (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog))
        (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest *
            (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo, _hhi⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p := cgOverlapDataConst_nonneg d s2 p hlo
  have hE10 : (0 : ℝ) ≤ recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE1Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  have hE20 : (0 : ℝ) ≤ recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog) :=
    recutPinnedE2Flux_nonneg M L omega m jn hsig (recutOrderBase M hlog)
  refine hlevel_of_energyBound (Cdata := cgOverlapDataConst d s2 p)
    (Cen := Cen0 * recutEnergyFactor M Y m omega)
    (Cw := 2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal)
    hsig (recutOrderBase M hlog).2.1 (by simpa only [recutOrderBase_val] using hss2)
    hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hCdata0 hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) le_rfl le_rfl ?_
  refine seamSplitOf_of_seam M Y m omega p s2 (Ccg := Ccg)
    (sbase := homS M) (kappa := 1) (theta := 1) (Cen0 := Cen0) (Ktest := Ktest)
    hCcg0 hs rfl hlog hgamma1 hCgap zero_le_one one_pos hCen0 hE10 hE20 hCdata0
    (by linarith only [hss2]) hs2gap ?_ ?_ ?_ hdom1 hdom2 hfin
  · rw [pairCwOf]
    have h2 := pairCwLegOf_nonneg d p s2 (Ccg := Ccg)
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

/-- **`hlevelDual` AT A FREE `Ccg`, THE `ã` COEFFICIENT AND THE BASE `s/8`.**

`HomSeamFluxLevelChain.recutHlevelDualFlux_of_seam` with the coarse-graining
constant freed. -/
theorem hlevelDualFluxAt_of_seam [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (m : ℤ) (jn : ℕ) {sigmaBarM : ℝ}
    (hsig : 0 < sigmaBarM) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (p : FiniteLpExponent) (s2 : FractionalOrder) {g : Vec d → Vec d}
    {Ccg Kg Kh KhInf S Cen0 Ktest : ℝ} (hCcg0 : 0 ≤ Ccg) (hs : 0 < homS M)
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
          coarseGrainingFinitePRHS Ccg
            (7 * (recutOrderBase M hlog).1 / 8) s2.1 sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m jn hsig (recutOrderBase M hlog))
            (recutPinnedDg m s2 p g) S ((originCube d m).scale - (jn : ℤ))) ≤
      Real.rpow 3 ((recutOrderBase M hlog).1 * (m : ℝ)) *
        (sigmaBarM *
          (2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest *
              (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal *
            dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  obtain ⟨hlo2, _hhi2⟩ := holderHalf_window (p := p) hs2lt hs2gt
  have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d s2 p :=
    cgOverlapDataConst_nonneg d s2 p hlo2
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
    (Cw := 2 * pairCwOf d Ccg p s2 Cgap Cen0 (homS M) Ktest)
    (EB := (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal)
    hsig (by simp only [recutOrderBase_val]; linarith only [hs])
    (by simp only [recutOrderBase_val]; linarith only [hss2, hs])
    (by simpa only [recutOrderBase_val] using hlodual)
    hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0
    (mul_nonneg hCen0 (recutEnergyFactor_nonneg M Y m omega)) hCdata0 hSbound
    (overlapSeminorm_toReal_le m s2 p hKg0 hs2lt hs2gt hKg) le_rfl le_rfl ?_
  refine seamSplitOf_of_seam M Y m omega p s2 (Ccg := Ccg)
    (sbase := homS M) (kappa := Ktest) (theta := 7 / 8) (Cen0 := Cen0) (Ktest := Ktest)
    hCcg0 hs rfl hlog hgamma1 hCgap hKtest0 (by norm_num) hCen0 hE10 hE20 hCdata0
    (by linarith only [hss2, hs]) hs2gap ?_ ?_ ?_ hdom1 hdom2 hfin
  · rw [pairCwOf]
    have h1 := pairCwLegOf_nonneg d p s2 (Ccg := Ccg)
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

/-! ## 3. The two monotonicity steps that make `max` compose -/

/-- The printed right-hand side is monotone UP in the coarse-graining constant,
at the signs the bundle's own conjuncts carry. -/
theorem coarseGrainingFinitePRHS_mono_ccg {Ccg Ccg' s s2 sigma E1 E2 Dg S : ℝ} (n : ℤ)
    (hCcg : Ccg ≤ Ccg') (hs : 0 < s) (hss2 : s < s2) (hE1 : 0 ≤ E1) (hDg : 0 ≤ Dg)
    (hS : 0 ≤ S) :
    coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n ≤
      coarseGrainingFinitePRHS Ccg' s s2 sigma E1 E2 Dg S n := by
  have hsinv : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hspow : (0 : ℝ) ≤ s ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hs.le _
  have hwin : (0 : ℝ) ≤ (s2 - s)⁻¹ := inv_nonneg.mpr (by linarith only [hss2])
  have hE2sq : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by
    have h2 : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := sq_nonneg E2
    linarith only [h2]
  have hthree : (0 : ℝ) ≤ (3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hDg
  have hA : (0 : ℝ) ≤ s⁻¹ * Real.sqrt sigma * E1 * S :=
    mul_nonneg (mul_nonneg (mul_nonneg hsinv (Real.sqrt_nonneg _)) hE1) hS
  have hB : (0 : ℝ) ≤ s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
      ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) :=
    mul_nonneg (mul_nonneg (mul_nonneg hspow hwin) hE2sq) hthree
  have h1 : Ccg * s⁻¹ * Real.sqrt sigma * E1 * S ≤
      Ccg' * s⁻¹ * Real.sqrt sigma * E1 * S := by
    calc Ccg * s⁻¹ * Real.sqrt sigma * E1 * S
        = Ccg * (s⁻¹ * Real.sqrt sigma * E1 * S) := by ring
      _ ≤ Ccg' * (s⁻¹ * Real.sqrt sigma * E1 * S) := mul_le_mul_of_nonneg_right hCcg hA
      _ = Ccg' * s⁻¹ * Real.sqrt sigma * E1 * S := by ring
  have h2 : Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
        ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) ≤
      Ccg' * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
        ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) := by
    calc Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)
        = Ccg * (s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
            ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)) := by ring
      _ ≤ Ccg' * (s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
            ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)) := mul_le_mul_of_nonneg_right hCcg hB
      _ = Ccg' * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
            ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) := by ring
  rw [coarseGrainingFinitePRHS, coarseGrainingFinitePRHS]
  linarith only [h1, h2]

/-- The bundle's own `Ccg` conjunct at any constant above the pin: this is what
makes `max Ccg₀ (recutPinnedCcgFlux d p)` an admissible entry point. -/
theorem cgDualBoundConstFlux_le_ofReal_of_pinned_le (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp2 : (2 : ℝ≥0∞) ≤ p.exponent) {Ccg : ℝ}
    (hCcg : recutPinnedCcgFlux d p ≤ Ccg) :
    cgDualBoundConstFlux d p ≤ ENNReal.ofReal Ccg :=
  le_trans (cgDualBoundConstFlux_dominates_self d hd p hp2)
    (ENNReal.ofReal_le_ofReal hCcg)

/-! ## 4. The core at a free `Ccg` -/

/-- `HomSeamFluxCoreSupply.SpineDatumRecutCoreFlux` with the coarse-graining
constant freed.  At `Ccg = recutPinnedCcgFlux d p` this is that definition. -/
def SpineDatumRecutCoreFluxAt [NeZero d] (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (sb : {s : ℝ // 0 < s})
    (sigmaBarM : ℝ) (hsig : 0 < sigmaBarM) (Kabs Ccg : ℝ)
    (p : FiniteLpExponent) (s2 : FractionalOrder)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      ∃ (jn : ℕ) (Cw S EB : ℝ) (s : FractionalOrder) (Fflux : Vec d → Vec d),
        0 < jn ∧ s.1 + (d : ℝ) / p.exponent.toReal ≤ 1 / 2 ∧
        7 * s.1 / 8 < s2.1 ∧ 0 ≤ Cw ∧
        spineClauseConst d s.1 p.exponent.toReal Cw (stepFourSchauderConstU d) ≤ Kabs ∧
        0 ≤ EB ∧
        ENNReal.ofReal EB ≤ ethmB M Cgap Y m (homN M m) sb omega ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingFinitePMultiscale (originCube d m) jn Ccg
            s.1 (s.1 / 4) s2.1 p.exponent.toReal sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig s)
            (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g)
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux) ∧
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
            (s.1 - s.1 / 4) jn N
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u) ≤
              S) ∧
        coarseGrainingFinitePRHS Ccg s.1 s2.1 sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig s)
            (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
            ((originCube d m).scale - (jn : ℤ)) ≤
          sigmaBarM *
            (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        cgTestConst d (originCube d m) s.1 (7 * s.1 / 8) p.conjugate.exponent.toReal *
            (Real.rpow 3 (7 * s.1 / 8 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg (7 * s.1 / 8) s2.1
                sigmaBarM (recutPinnedE1Flux M L omega m jn hsig s)
                (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 (s.1 * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-- **THE INSTALLED `ã` BUNDLE, AT A FREE `Ccg`.**

`HomSeamFluxCoreSupply.spineDatumCoarseGrainingRecutFlux_of_core` with the
coarse-graining constant freed.  The pinned proof's two uses of the pin —
`recutPinnedCcgFlux_nonneg` and `cgDualBoundConstFlux_dominates_self` — become
the two hypotheses `hCcg0` and `hCcgDom`. -/
theorem spineDatumCoarseGrainingRecutFluxAt_of_core [NeZero d]
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs Ccg : ℝ} (hsig : 0 < sigmaBarM)
    (p : FiniteLpExponent) (s2 : FractionalOrder) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1) (hCcg0 : 0 ≤ Ccg)
    (hCcgDom : cgDualBoundConstFlux d p ≤ ENNReal.ofReal Ccg)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCoreFluxAt M Cgap Y m sb sigmaBarM hsig Kabs Ccg p s2 omega) :
    SpineDatumCoarseGrainingRecutFlux M Cgap Y m sb sigmaBarM hsig Kabs omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨jn, Cw, S, EB, s, Fflux, hjn0, hguard, hwin, hCw, hKabsC, hEB, hdom,
    hCGm, hS0, hS, hlevel, hlevelDual⟩ :=
    hcore L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hgmem : MemCubeEuclideanFullWsp (originCube d m) s2 p g :=
    memCubeEuclideanFullWsp_of_holderHalf hKg0 hs2lt hs2gt hKg
  refine ⟨jn, Cw, Ccg, recutPinnedE1Flux M L omega m jn hsig s,
    recutPinnedE2Flux M L omega m jn hsig s, recutPinnedDg m s2 p g, S, EB, p, s,
    recutOrderLow s, recutOrderDual s, s2, Fflux, hjn0, hguard, hCw, hKabsC, hEB, hdom,
    rfl, rfl, hwin, hs2lt, hs2gt, hCGm, hS0, hS, hlevel, hCcg0,
    recutPinnedE1Flux_nonneg M L omega m jn hsig s,
    recutPinnedE2Flux_nonneg M L omega m jn hsig s,
    recutPinnedDg_nonneg m s2 p g, hCcgDom, ?_, ?_, ?_, hlevelDual⟩
  · exact parentErrorOne_dominates_self (originCube d m) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) hsig (recutOrderLow s)
  · exact parentErrorTwo_dominates_self (originCube d m) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) hsig
      (fractionalOrderHalf (recutOrderLow s))
  · exact overlapSeminorm_dominates_self (originCube d m) s2 p hgmem

/-- **THE INSTALLED `ã` BUNDLE AT THE NUMERAL PIN AND A FREE `Ccg`.** -/
theorem spineDatumCoarseGrainingRecutFluxAt_of_core_pinned [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs Ccg : ℝ} (hsig : 0 < sigmaBarM)
    (hCcg0 : 0 ≤ Ccg)
    (hCcgDom : cgDualBoundConstFlux d (recutExponent d (le_trans (by norm_num) hd)) ≤
      ENNReal.ofReal Ccg)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCoreFluxAt M Cgap Y m sb sigmaBarM hsig Kabs Ccg
      (recutExponent d (le_trans (by norm_num) hd)) recutOrderTop omega) :
    SpineDatumCoarseGrainingRecutFlux M Cgap Y m sb sigmaBarM hsig Kabs omega := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨hlt, hgt⟩ := recutOrderTop_window d hd1
  exact spineDatumCoarseGrainingRecutFluxAt_of_core M Cgap Y m sb hsig
    (recutExponent d hd1) recutOrderTop hlt hgt hCcg0 hCcgDom omega hcore

/-! ## 4. The supply at a free `Ccg`, and the producer -/

/-- `HomSeamFluxCoreSupply.RecutCoreSupplyFlux` with the coarse-graining constant
freed: the multiscale clause may be delivered at ANY constant. -/
def RecutCoreSupplyFluxAt [NeZero d] (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m : ℤ) (Cen0 Ccg : ℝ)
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
            Ccg (homS M) (homS M / 4)
            (recutOrderTop : FractionalOrder).1 (recutExponent d hd1).exponent.toReal
            ((Annealed.sigmaBar M m : ℝ))
            (recutPinnedE1Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedDg m recutOrderTop (recutExponent d hd1) g)
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux) ∧
        FluxCorrectedParentIdentification M m (homK M) omega

/-- **THE TWELVE-CONJUNCT `ã` CORE AT A FREE `Ccg`, PRODUCED.**

`HomSeamFluxCoreSupply.spineDatumRecutCoreFlux_of_supply` with the
coarse-graining constant freed; the `K_abs` frame condition is asked at the
matching pairing constant `recutCwFluxAt`. -/
theorem spineDatumRecutCoreFluxAt_of_supply [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d)
    {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    {Kabs Cen0 Ccg : ℝ} (hCcg0 : 0 ≤ Ccg)
    (omega : Cutoff.CutoffSample d) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤)
    (hKabs : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
        (recutCwFluxAt d hd1 M Ccg Cgap Cen0) (stepFourSchauderConstU d) ≤ Kabs)
    (hsupply : RecutCoreSupplyFluxAt M Y m Cen0 Ccg hd1 hlog omega) :
    SpineDatumRecutCoreFluxAt M Cgap Y m (homSeamBase M hs)
      ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 Kabs Ccg
      (recutExponent d hd1) recutOrderTop omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨S, Fflux, hS0, hS, hSbound, hCGm, hid⟩ :=
    hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hcen : cubeCenter (originCube d m) ∈ openCubeSet (originCube d m) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  have hKhInf0 : (0 : ℝ) ≤ KhInf :=
    le_trans (norm_nonneg _) (hKhInf (cubeCenter (originCube d m)) hcen)
  have hdom1 := seamDom1Flux_of_identification M m (homK M) omega hs hlog hid L hL
  have hdom2 := seamDom2Flux_of_identification M m (homK M) omega hs hlog hid L hL
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 :=
    recutExponent_quotient d hd1
  have hguard : homS M + (d : ℝ) / (recutExponent d hd1).exponent.toReal ≤ 1 / 2 := by
    rw [hquot]; linarith only [hquarter]
  have hss2 : homS M < (recutOrderTop : FractionalOrder).1 := by
    rw [recutOrderTop_val]; linarith only [hquarter]
  obtain ⟨hs2lt, hs2gt⟩ := recutOrderTop_window d hd1
  have hgapexp := recutOrderTop_gapExponent
  have hhalf : homS M / 2 ≤ 7 * homS M / 8 := by linarith only [hs]
  have hlts : 7 * homS M / 8 < homS M := by linarith only [hs]
  obtain ⟨hlodual, _hhidual⟩ :=
    cgOrderWindow_of_guard (p := recutExponent d hd1) hd1 hs hguard hhalf hlts
  have hKtest0 : (0 : ℝ) ≤ recutPinnedKtest d hd1 M :=
    cgTestConstBase_nonneg d hlodual
  have hCw0 : (0 : ℝ) ≤ recutCwFluxAt d hd1 M Ccg Cgap Cen0 :=
    recutCwFluxAt_nonneg hd1 M hCcg0 hs hlog hCgap hCen0
  have hjn : (originCube d m).scale - ((homK M : ℕ) : ℤ) = homN M m := rfl
  refine ⟨homK M, recutCwFluxAt d hd1 M Ccg Cgap Cen0, S,
    (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal, recutOrderBase M hlog,
    Fflux, homK_pos hlog, hguard, ?_, hCw0, hKabs, ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal_le, hCGm, hS0, hS, ?_, ?_⟩
  · simp only [recutOrderBase_val]
    linarith only [hss2, hs]
  · exact hlevelFluxAt_of_seam M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hCcg0 hs hlog hgamma1 hCgap hss2 hs2lt hs2gt
      hgapexp hKtest0 hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin
  · exact hlevelDualFluxAt_of_seam hd1 M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hCcg0 hs hlog hgamma1 hCgap hguard hss2 hs2lt
      hs2gt hgapexp rfl hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin

end

end Algsuperdiff.Section4.Provider.Homogenization
