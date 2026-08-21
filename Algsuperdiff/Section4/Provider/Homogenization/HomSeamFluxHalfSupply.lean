/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfBundle

/-!
# The core and the supply at the re-pinned gauge, and the model-free `K_abs`

## What this file supplies

`HomSeamFluxFreeCcg`'s core/supply layer, re-cut at the Schauder gauge
`α = 1/2`:

* `SpineDatumRecutCoreFluxAtHalf` — the twelve-conjunct core with `hlevelDual`
  at `α = 1/2`;
* `spineDatumCoarseGrainingRecutFluxAtHalf_of_core` — core ⇒ bundle;
* `spineDatumRecutCoreFluxAtHalf_of_supply` — supply ⇒ core, at the re-pinned
  pairing constant `recutCwHalfFluxAt`.  The SUPPLY is UNCHANGED: this file
  consumes `HomSeamFluxFreeCcg.RecutCoreSupplyFluxAt` verbatim, so the re-cut
  costs the multiscale-clause producer nothing;
* `spineDatumRecutCoreFluxAtHalf_of_supply_envelope` — the same, with the
  `K_abs` frame condition asked at a constant fixed BEFORE the model:
  `(2 C_sch + 288 d²) · recutCwHalfEnvelope d hd1 Ccg Cgap Cen0`.

That last statement is the point of the D2 re-cut.  At the `α = s` pin
the analogous frame condition is unsatisfiable uniformly in `M`
(`recutPinnedKtest → ∞`); here the constant names `d`, the printed
exponent `p = 4d`, `C_gap` and `C_en⁰` and nothing else.

`C_en⁰` remains a free slot.  Whether the energy-slot constant supplied for it
is itself model-uniform is a SEPARATE question, still open; nothing here
asserts that it is.
-/

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The core at a free `Ccg` and the gauge `α = 1/2` -/

/-- `HomSeamFluxFreeCcg.SpineDatumRecutCoreFluxAt` with `hlevelDual` read at the
Schauder gauge `α = 1/2`.  Every other conjunct is verbatim. -/
def SpineDatumRecutCoreFluxAtHalf [NeZero d] (M : ABKModel d) (Cgap : ℝ)
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
        cgTestConst d (originCube d m) (1 / 2) (7 * s.1 / 8)
            p.conjugate.exponent.toReal *
            (Real.rpow 3 (7 * s.1 / 8 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg (7 * s.1 / 8) s2.1
                sigmaBarM (recutPinnedE1Flux M L omega m jn hsig s)
                (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-- **THE INSTALLED `ã` BUNDLE AT THE RE-PINNED GAUGE AND A FREE `Ccg`.**

`HomSeamFluxFreeCcg.spineDatumCoarseGrainingRecutFluxAt_of_core` with the two
`α`-slots moved; the proof is unchanged. -/
theorem spineDatumCoarseGrainingRecutFluxAtHalf_of_core [NeZero d]
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs Ccg : ℝ} (hsig : 0 < sigmaBarM)
    (p : FiniteLpExponent) (s2 : FractionalOrder) (hs2lt : s2.1 < 1 / 2)
    (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1) (hCcg0 : 0 ≤ Ccg)
    (hCcgDom : cgDualBoundConstFlux d p ≤ ENNReal.ofReal Ccg)
    (omega : Cutoff.CutoffSample d)
    (hcore :
      SpineDatumRecutCoreFluxAtHalf M Cgap Y m sb sigmaBarM hsig Kabs Ccg p s2 omega) :
    SpineDatumCoarseGrainingRecutFluxHalf M Cgap Y m sb sigmaBarM hsig Kabs omega := by
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

/-- **THE INSTALLED BUNDLE AT THE NUMERAL PIN, THE RE-PINNED GAUGE AND A FREE
`Ccg`.** -/
theorem spineDatumCoarseGrainingRecutFluxAtHalf_of_core_pinned [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs Ccg : ℝ} (hsig : 0 < sigmaBarM)
    (hCcg0 : 0 ≤ Ccg)
    (hCcgDom : cgDualBoundConstFlux d (recutExponent d (le_trans (by norm_num) hd)) ≤
      ENNReal.ofReal Ccg)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCoreFluxAtHalf M Cgap Y m sb sigmaBarM hsig Kabs Ccg
      (recutExponent d (le_trans (by norm_num) hd)) recutOrderTop omega) :
    SpineDatumCoarseGrainingRecutFluxHalf M Cgap Y m sb sigmaBarM hsig Kabs omega := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨hlt, hgt⟩ := recutOrderTop_window d hd1
  exact spineDatumCoarseGrainingRecutFluxAtHalf_of_core M Cgap Y m sb hsig
    (recutExponent d hd1) recutOrderTop hlt hgt hCcg0 hCcgDom omega hcore

/-! ## 2. The producer, from the UNCHANGED supply -/

/-- **THE TWELVE-CONJUNCT `ã` CORE AT THE RE-PINNED GAUGE, PRODUCED.**

`HomSeamFluxFreeCcg.spineDatumRecutCoreFluxAt_of_supply` with the `K_test` slot
at the Schauder gauge.  The supply hypothesis is the SAME object
(`RecutCoreSupplyFluxAt`): the re-cut asks the multiscale-clause producer for
nothing new. -/
theorem spineDatumRecutCoreFluxAtHalf_of_supply [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d)
    {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    {Kabs Cen0 Ccg : ℝ} (hCcg0 : 0 ≤ Ccg)
    (omega : Cutoff.CutoffSample d) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤)
    (hKabs : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
        (recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0) (stepFourSchauderConstU d) ≤ Kabs)
    (hsupply : RecutCoreSupplyFluxAt M Y m Cen0 Ccg hd1 hlog omega) :
    SpineDatumRecutCoreFluxAtHalf M Cgap Y m (homSeamBase M hs)
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
  have hKtest0 : (0 : ℝ) ≤ recutKtestHalf d hd1 M := recutKtestHalf_nonneg d hd1 M hlog
  have hCw0 : (0 : ℝ) ≤ recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0 := by
    obtain ⟨hs2lt', hs2gt'⟩ := recutOrderTop_window d hd1
    have hCdata0 : (0 : ℝ) ≤ cgOverlapDataConst d recutOrderTop (recutExponent d hd1) :=
      cgOverlapDataConst_nonneg d recutOrderTop (recutExponent d hd1)
        (holderHalf_window (p := recutExponent d hd1) hs2lt' hs2gt').1
    have h1 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop (Ccg := Ccg)
      (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M) (kappa := 1) (theta := 1)
      hCcg0 hCgap hCen0 hs zero_le_one one_pos (by linarith only [hss2]) hCdata0 hgapexp
    have h2 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop (Ccg := Ccg)
      (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M)
      (kappa := recutKtestHalf d hd1 M) (theta := 7 / 8) hCcg0 hCgap hCen0 hs hKtest0
      (by norm_num) (by linarith only [hss2, hs]) hCdata0 hgapexp
    rw [recutCwHalfFluxAt, pairCwOf]
    linarith only [h1, h2]
  have hjn : (originCube d m).scale - ((homK M : ℕ) : ℤ) = homN M m := rfl
  refine ⟨homK M, recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0, S,
    (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal, recutOrderBase M hlog,
    Fflux, homK_pos hlog, hguard, ?_, hCw0, hKabs, ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal_le, hCGm, hS0, hS, ?_, ?_⟩
  · simp only [recutOrderBase_val]
    linarith only [hss2, hs]
  · exact hlevelFluxAt_of_seam M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hCcg0 hs hlog hgamma1 hCgap hss2 hs2lt hs2gt
      hgapexp hKtest0 hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin
  · exact hlevelDualHalfFluxAt_of_seam M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hCcg0 hs hlog hgamma1 hCgap hss2 hs2lt
      hs2gt hgapexp rfl hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin

/-! ## 3. THE MODEL-FREE FRAME CONDITION -/

/-- **THE CORE, AT A `K_abs` FIXED BEFORE THE MODEL.**

The same producer with the frame condition asked at the envelope constant
`(2 C_sch + 288 d²) · recutCwHalfEnvelope d hd1 Ccg Cgap Cen0`, which mentions
only `d`, the printed exponent, `C_gap` and `C_en⁰` — no `M`, hence no `γ`.

This is the statement the item 4 measured to be UNSATISFIABLE at the `α = s`
pin. -/
theorem spineDatumRecutCoreFluxAtHalf_of_supply_envelope [NeZero d] (hd1 : 1 ≤ d)
    (M : ABKModel d) {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (hs : 0 < homS M) {Kabs Cen0 Ccg : ℝ} (hCcg0 : 0 ≤ Ccg)
    (omega : Cutoff.CutoffSample d) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤)
    (hKabs : (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
      recutCwHalfEnvelope d hd1 Ccg Cgap Cen0 ≤ Kabs)
    (hsupply : RecutCoreSupplyFluxAt M Y m Cen0 Ccg hd1 hlog omega) :
    SpineDatumRecutCoreFluxAtHalf M Cgap Y m (homSeamBase M hs)
      ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 Kabs Ccg
      (recutExponent d hd1) recutOrderTop omega :=
  spineDatumRecutCoreFluxAtHalf_of_supply hd1 M Y m hs hCcg0 omega hlog hgamma1 hCgap
    hCen0 hfin
    (le_trans (spineClauseConst_le_abs_half d hd1 M hCcg0 hCgap hCen0 hlog) hKabs)
    hsupply

/-- **THE `K_abs` SLOT, EXISTENTIALLY, BEFORE THE MODEL.**

The frame condition of the re-cut lane admits a witness quantified OUTSIDE the
model quantifier — the shape `HomSpineFinalEndpoint` and the recurrence need,
and the one the `α = s` pin cannot produce. -/
theorem exists_kabs_uniform_half (d : ℕ) (hd1 : 1 ≤ d) {Ccg Cgap Cen0 : ℝ}
    (hCcg0 : 0 ≤ Ccg) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) :
    ∃ Kabs : ℝ, 0 ≤ Kabs ∧
      ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
        spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
          (recutCwHalfFluxAt d hd1 M Ccg Cgap Cen0) (stepFourSchauderConstU d) ≤ Kabs := by
  refine ⟨(2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
    recutCwHalfEnvelope d hd1 Ccg Cgap Cen0, ?_,
    fun M hlog => spineClauseConst_le_abs_half d hd1 M hCcg0 hCgap hCen0 hlog⟩
  have hU : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
  have hd2 : (0 : ℝ) ≤ 288 * (d : ℝ) ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hsq]
  exact mul_nonneg (by linarith only [hU, hd2])
    (recutCwHalfEnvelope_nonneg d hd1 hCcg0 hCgap hCen0)

end

end Algsuperdiff.Section4.Provider.Homogenization
