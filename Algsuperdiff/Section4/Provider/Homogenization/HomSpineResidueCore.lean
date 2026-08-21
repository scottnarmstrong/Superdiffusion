/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueLevel

/-!
# The re-cut core, produced: all twelve conjuncts at the corrected pin

## What this file supplies

`HomSpineInstallPins.SpineDatumRecutCore` is the twelve-conjunct core of the
§4.5 bundle.  `spineDatumRecutCore_of_supply` produces ALL twelve at the
corrected numeral pin `p = 4d`, `s = |log γ|⁻¹`, `s₂ = 49/100`, `j_n = ⌈10|log
γ|⌉`, from one per-`ω` supplier `RecutCoreSupply` and a frame condition on
`K_abs`:

| conjunct | where it comes from |
|:-- |:-- |
| `0 < j_n`, the guard, the window, `0 ≤ C_w` | the numeral pin (proved here) |
| `spineClauseConst … ≤ K_abs` | `hKabs`, a frame condition on the free `K_abs` |
| `0 ≤ E_B`, `ofReal E_B ≤ EthmB(m)` | the real cut of `EthmB(m)` (proved here) |
| the MULTISCALE clause | `RecutCoreSupply` (the coarse-graining input) |
| `0 ≤ S`, the partial sums | `RecutCoreSupply` |
| `hlevel`, `hlevelDual` | `HomSpineResidueLevel` (the `EthmB(m)` pairing) |

So the residual bill of Theorem B's §4.5 spine is exactly `RecutCoreSupply` plus
`hfin` and `hKabs`.

## The residual bill, itemized

`RecutCoreSupply` asks, for each `L ≥ m` and each printed elliptic pair, for

1. the energy partial-sum slot `S` with the printed bound `hSbound` at the
   Step-2 constant shape `C · 3^{(1-α)X_m}(1 + 𝓔_{1/4})` — **this is the
   Theorem-C item**;
2. the MULTISCALE coarse-graining clause at `Gen:= printedLocalEnergy`;
3. the two `𝓔`-dominations — **the carrier seam**, disclosed in
   `HomSpineResiduePairing` and NOT dischargeable at the current pins.

`hfin` is the a.e. finiteness of the `[0,∞]` carrier, which
`HomSpineFinalWitness` already derives from the `p = 1` moment.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The pinned constants -/

/-- The test-class constant of the dual level condition, at the printed pin. -/
def recutPinnedKtest (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d) : ℝ :=
  cgTestConstBase d (homS M) (7 * homS M / 8)
    (recutExponent d hd1).conjugate.exponent.toReal

/-- **THE PINNED `C_w`**: `recutPairCw` at `p = 4d`, `s₂ = 49/100`,
`s = |log γ|⁻¹`. -/
def recutPinnedCw (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d) (Cgap Cen0 : ℝ) : ℝ :=
  recutPairCw d (recutExponent d hd1) recutOrderTop Cgap Cen0 (homS M)
    (recutPinnedKtest d hd1 M)

/-! ## 2. The residual bill -/

/-- **THE SUPPLIER.**  What the §4.5 spine still needs, per `ω`: the energy
partial-sum slot with the Step-2 bound (the Theorem-C item), the multiscale
coarse-graining clause, and the two `𝓔`-dominations (the carrier seam). -/
def RecutCoreSupply [NeZero d] (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m : ℤ) (hs : 0 < homS M) (sigmaBarM : ℝ) (hsig : 0 < sigmaBarM) (Cen0 : ℝ)
    (hd1 : 1 ≤ d) (hlog : 4 ≤ |Real.log M.gamma|)
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
      ∃ (S : ℝ) (Fflux : Vec d → Vec d),
        0 ≤ S ∧
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m)
              (recutExponent d hd1).exponent.toReal (homS M - homS M / 4) (homK M) N
              (printedLocalEnergy
                (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) ≤ S) ∧
        S ≤ Cen0 * recutEnergyFactor M Y m omega *
            energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ∧
        (∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingFinitePMultiscale (originCube d m) (homK M)
            (recutPinnedCcg d (recutExponent d hd1)) (homS M) (homS M / 4)
            (recutOrderTop : FractionalOrder).1 (recutExponent d hd1).exponent.toReal
            sigmaBarM
            (recutPinnedE1 M L omega m (homK M) hsig (recutOrderBase M hlog))
            (recutPinnedE2 M L omega m (homK M) hsig (recutOrderBase M hlog))
            (recutPinnedDg m recutOrderTop (recutExponent d hd1) g)
            (printedLocalEnergy
              (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) G Fflux) ∧
        ENNReal.ofReal
            (recutPinnedE1 M L omega m (homK M) hsig (recutOrderBase M hlog)) ≤
          fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
            (homHalf ⟨homS M, hs⟩) omega ∧
        ENNReal.ofReal
            (recutPinnedE2 M L omega m (homK M) hsig (recutOrderBase M hlog)) ≤
          fluxCorrectedTwoScaleErrorObservableSup M m (homN M m)
            (homQuarterOf ⟨homS M, hs⟩) omega

/-! ## 3. The numeral pin, checked -/

/-- The printed mesoscale depth is positive (`⌈10|log γ|⌉ ≥ 40`). -/
theorem homK_pos {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|) : 0 < homK M := by
  have h := homK_ge M
  have h40 : (40 : ℝ) ≤ (homK M : ℝ) := by linarith only [h, hlog]
  by_contra hcon
  push_neg at hcon
  have hzero : homK M = 0 := Nat.le_zero.mp hcon
  rw [hzero] at h40
  norm_num at h40

/-- `d / (4d) = 1/4`: the printed exponent's own quotient. -/
theorem recutExponent_quotient (d : ℕ) (hd1 : 1 ≤ d) :
    (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith only [hdR]
  rw [recutExponent_toReal d hd1]
  field_simp

/-- The corrected pin absorbs the mesoscale gap at the `γ⁵` rate. -/
theorem recutOrderTop_gapExponent :
    5 < 10 * (recutOrderTop : FractionalOrder).1 * Real.log 3 := by
  rw [recutOrderTop_val]
  exact gapExponent_holds_at_fortyNineHundredths

/-! ## 4. THE PRODUCER -/

/-- **THE TWELVE-CONJUNCT CORE, PRODUCED.**

Everything the `SpineDatumRecutCore` asks for, at the corrected numeral pin,
from `RecutCoreSupply`, the a.e. finiteness of `EthmB(m)` and the `K_abs` frame
condition.  Composing with
`HomSpineInstallPins.spineDatumCoarseGrainingRecut_of_core_pinned` and
`homogenization_spine_close_of_recutCore` carries it to the spine endpoint. -/
theorem spineDatumRecutCore_of_supply [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d)
    {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    {sigmaBarM Kabs Cen0 : ℝ} (hsig : 0 < sigmaBarM)
    (omega : Cutoff.CutoffSample d) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hfin : ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ≠ ⊤)
    (hKabs : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
        (recutPinnedCw d hd1 M Cgap Cen0) (stepFourSchauderConst d (homS M)) ≤ Kabs)
    (hsupply : RecutCoreSupply M Y m hs sigmaBarM hsig Cen0 hd1 hlog omega) :
    SpineDatumRecutCore M Cgap Y m hs sigmaBarM hsig Kabs (recutExponent d hd1)
      recutOrderTop omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨S, Fflux, hS0, hS, hSbound, hCGm, hdom1, hdom2⟩ :=
    hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  /- the data signs, from the root's own binde -/
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hcen : cubeCenter (originCube d m) ∈ openCubeSet (originCube d m) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  have hKhInf0 : (0 : ℝ) ≤ KhInf :=
    le_trans (norm_nonneg _) (hKhInf (cubeCenter (originCube d m)) hcen)
  /- the numeral fra -/
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 :=
    recutExponent_quotient d hd1
  have hguard : homS M + (d : ℝ) / (recutExponent d hd1).exponent.toReal ≤ 1 / 2 := by
    rw [hquot]; linarith only [hquarter]
  have hss2 : homS M < (recutOrderTop : FractionalOrder).1 := by
    rw [recutOrderTop_val]; linarith only [hquarter]
  obtain ⟨hs2lt, hs2gt⟩ := recutOrderTop_window d hd1
  have hgapexp := recutOrderTop_gapExponent
  have hCdata0 : (0 : ℝ) ≤
      cgOverlapDataConst d recutOrderTop (recutExponent d hd1) :=
    cgOverlapDataConst_nonneg d recutOrderTop (recutExponent d hd1)
      (holderHalf_window (p := recutExponent d hd1) hs2lt hs2gt).1
  have hhalf : homS M / 2 ≤ 7 * homS M / 8 := by linarith only [hs]
  have hlts : 7 * homS M / 8 < homS M := by linarith only [hs]
  obtain ⟨hlodual, _hhidual⟩ :=
    cgOrderWindow_of_guard (p := recutExponent d hd1) hd1 hs hguard hhalf hlts
  have hKtest0 : (0 : ℝ) ≤ recutPinnedKtest d hd1 M :=
    cgTestConstBase_nonneg d hlodual
  have hCw0 : (0 : ℝ) ≤ recutPinnedCw d hd1 M Cgap Cen0 := by
    have h1 := recutPairCwLeg_nonneg d (recutExponent d hd1) recutOrderTop
      (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M) (kappa := 1) (theta := 1)
      hCgap hCen0 hs zero_le_one one_pos (by linarith only [hss2]) hCdata0 hgapexp
    have h2 := recutPairCwLeg_nonneg d (recutExponent d hd1) recutOrderTop
      (Cgap := Cgap) (Cen0 := Cen0) (sbase := homS M)
      (kappa := recutPinnedKtest d hd1 M) (theta := 7 / 8) hCgap hCen0 hs hKtest0
      (by norm_num) (by linarith only [hss2, hs]) hCdata0 hgapexp
    rw [recutPinnedCw, recutPairCw]
    linarith only [h1, h2]
  have hjn : (originCube d m).scale - ((homK M : ℕ) : ℤ) = homN M m := rfl
  refine ⟨homK M, recutPinnedCw d hd1 M Cgap Cen0, S,
    (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal, recutOrderBase M hlog,
    Fflux, homK_pos hlog, hguard, ?_, hCw0, hKabs, ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal_le, hCGm, hS0, hS, ?_, ?_⟩
  · simp only [recutOrderBase_val]
    linarith only [hss2, hs]
  · exact recutHlevel_of_seam M L omega m (homK M) hsig Y (recutExponent d hd1)
      recutOrderTop hs hlog hgamma1 hCgap hss2 hs2lt hs2gt hgapexp hKtest0 hKg hKhInf0
      hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin
  · exact recutHlevelDual_of_seam hd1 M L omega m (homK M) hsig Y (recutExponent d hd1)
      recutOrderTop hs hlog hgamma1 hCgap hguard hss2 hs2lt hs2gt hgapexp rfl hKg
      hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin

end

end Algsuperdiff.Section4.Provider.Homogenization
