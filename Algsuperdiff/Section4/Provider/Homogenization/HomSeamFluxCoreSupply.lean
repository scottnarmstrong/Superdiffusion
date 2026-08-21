/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxBundle
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxLevelChain
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueCore

/-!
# The re-cut core and its residual bill, at `ã_{L,m}` and the base `s/8`

## What this file supplies

The print-accurate successors of `HomSpineInstallPins.SpineDatumRecutCore` and
`HomSpineResidueCore.RecutCoreSupply`:

```text
  SpineDatumRecutCoreFlux   —  the twelve-conjunct core at the printed
                               coefficient ã_{L,m}, the s-free Schauder
                               constant, and a free EthmB base `sb`;
  RecutCoreSupplyFlux       —  what the §4.5 spine still needs, per ω.
```

`spineDatumRecutCoreFlux_of_supply` produces the core at the corrected numeral
pin `p = 4d`, `s = |log γ|⁻¹`, `s₂ = 49/100`, `j_n = ⌈10|log γ|⌉` and at the
re-pinned base `s' = s/8`, from `RecutCoreSupplyFlux` alone (plus `hfin` and the
`K_abs` frame condition).

## The residual bill, itemized

`RecutCoreSupplyFlux` asks, for each `L ≥ m` and each printed elliptic pair, for

1. `0 ≤ S` and the energy partial-sum slot `S` at `Gen:= printedLocalEnergy`
   read at `ã` — which, by
   `HomSeamFluxCoefficient.printedLocalEnergy_fluxCorrected`, is the SAME
   function of cubes as at `a_L`, so the producers apply verbatim;
2. `hSbound`, the printed Step-2 bound on `S` at the constant shape
   `C · 3^{(1-α)X_m}(1 + 𝓔_{1/4})` — the sub-cube average, whose own
   upstream is the top-scale item `htop_of_stepTwoA_enlargedY`;
3. the MULTISCALE coarse-graining clause at the `ã` slots — the
   `exists_coarseGrainingFinitePMultiscale_of_cz`;
   (`HomSpineCzGridGauge`) its residual is no longer `CzFluxMultiscale`
   itself but exactly `GridDualTestFamily d p CA` (equivalently the gauge
   converse `NegativeBesovGridSmoothDualConverse`), on the range
   `s·p' < 1` — see `exists_coarseGrainingFinitePMultiscale_of_testFamily`;
4. `FluxCorrectedParentIdentification` — the ONE honest coefficient input of
   `HomSeamFluxCoefficient`; PRODUCED a.e. with no hypotheses
   (`HomSeamFluxIdentification.ae_fluxCorrectedParentIdentification`).

The two `𝓔`-dominations of the `RecutCoreSupply` are GONE: they are
produced here from item 4 by `seamDom1Flux_of_identification` and
`seamDom2Flux_of_identification`.

## What is NOT carried here

The `EthmB(m)` base is left free precisely because the re-pin moves it from
the printed `s` to `s/8`, and the spine's own defect witness
(`HomSpineFinalWitness.exists_spine_defect_witness`) is built from the Step-1
moment bound at the PRINTED base.  Closing the chain at `sb = homSeamBase M hs`
therefore needs the `s/8` moment sibling (numerals `128` / `64 d |log γ|`),
which is supplied elsewhere and is NOT asserted anywhere in this file.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The pinned `C_w` of the `ã` chain -/

/-- **THE PINNED `C_w` OF THE PRINT-FAITHFUL CHAIN**: `pairCwOf` at
`p = 4d`, `s₂ = 49/100`, `s = |log γ|⁻¹`, doubled to absorb the `√2` of the
second domination. -/
def recutPinnedCwFlux (d : ℕ) (hd1 : 1 ≤ d) (M : ABKModel d) (Cgap Cen0 : ℝ) : ℝ :=
  2 * pairCwOf d (recutPinnedCcgFlux d (recutExponent d hd1)) (recutExponent d hd1)
    recutOrderTop Cgap Cen0 (homS M) (recutPinnedKtest d hd1 M)

/-! ## 2. The reduced core at the printed coefficient -/

/-- **THE CONTENT-BEARING CORE OF THE `ã` BUNDLE.**

`HomSpineInstallPins.SpineDatumRecutCore` with the four slots read at the
printed flux-corrected field, the Schauder constant taken `s`-free, and the
`EthmB(m)` base left as a parameter. -/
def SpineDatumRecutCoreFlux [NeZero d] (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (sb : {s : ℝ // 0 < s})
    (sigmaBarM : ℝ) (hsig : 0 < sigmaBarM) (Kabs : ℝ)
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
          CoarseGrainingFinitePMultiscale (originCube d m) jn (recutPinnedCcgFlux d p)
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
        coarseGrainingFinitePRHS (recutPinnedCcgFlux d p) s.1 s2.1 sigmaBarM
            (recutPinnedE1Flux M L omega m jn hsig s)
            (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
            ((originCube d m).scale - (jn : ℤ)) ≤
          sigmaBarM *
            (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        cgTestConst d (originCube d m) s.1 (7 * s.1 / 8) p.conjugate.exponent.toReal *
            (Real.rpow 3 (7 * s.1 / 8 * (m : ℝ)) *
              coarseGrainingFinitePRHS (recutPinnedCcgFlux d p) (7 * s.1 / 8) s2.1
                sigmaBarM (recutPinnedE1Flux M L omega m jn hsig s)
                (recutPinnedE2Flux M L omega m jn hsig s) (recutPinnedDg m s2 p g) S
                ((originCube d m).scale - (jn : ℤ))) ≤
          Real.rpow 3 (s.1 * (m : ℝ)) *
            (sigmaBarM *
              (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))

/-! ## 3. The installation -/

/-- **THE INSTALLED `ã` BUNDLE.**

The four slot dominations of `SpineDatumCoarseGrainingRecutFlux` are DISCHARGED
at the printed carriers' own `toReal`, and the numeral frame is discharged from
the window hypotheses.  Nothing is assumed beyond `SpineDatumRecutCoreFlux`. -/
theorem spineDatumCoarseGrainingRecutFlux_of_core [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM)
    (p : FiniteLpExponent) (s2 : FractionalOrder) (hp2 : (2 : ℝ≥0∞) ≤ p.exponent)
    (hs2lt : s2.1 < 1 / 2) (hs2gt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCoreFlux M Cgap Y m sb sigmaBarM hsig Kabs p s2 omega) :
    SpineDatumCoarseGrainingRecutFlux M Cgap Y m sb sigmaBarM hsig Kabs omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨jn, Cw, S, EB, s, Fflux, hjn0, hguard, hwin, hCw, hKabsC, hEB, hdom,
    hCGm, hS0, hS, hlevel, hlevelDual⟩ :=
    hcore L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hgmem : MemCubeEuclideanFullWsp (originCube d m) s2 p g :=
    memCubeEuclideanFullWsp_of_holderHalf hKg0 hs2lt hs2gt hKg
  refine ⟨jn, Cw, recutPinnedCcgFlux d p, recutPinnedE1Flux M L omega m jn hsig s,
    recutPinnedE2Flux M L omega m jn hsig s, recutPinnedDg m s2 p g, S, EB, p, s,
    recutOrderLow s, recutOrderDual s, s2, Fflux, hjn0, hguard, hCw, hKabsC, hEB, hdom,
    rfl, rfl, hwin, hs2lt, hs2gt, hCGm, hS0, hS, hlevel, recutPinnedCcgFlux_nonneg d p,
    recutPinnedE1Flux_nonneg M L omega m jn hsig s,
    recutPinnedE2Flux_nonneg M L omega m jn hsig s,
    recutPinnedDg_nonneg m s2 p g, ?_, ?_, ?_, ?_, hlevelDual⟩
  · exact cgDualBoundConstFlux_dominates_self d hd p hp2
  · exact parentErrorOne_dominates_self (originCube d m) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) hsig (recutOrderLow s)
  · exact parentErrorTwo_dominates_self (originCube d m) (recutParentScale m jn)
      (fluxCorrectedCoeffOn M L m (originCube d m) omega) hsig
      (fractionalOrderHalf (recutOrderLow s))
  · exact overlapSeminorm_dominates_self (originCube d m) s2 p hgmem

/-- **THE INSTALLED `ã` BUNDLE AT THE PRINTED NUMERAL PIN** `p = 4d`,
`s₁′ = s/8`, `s′ = 7s/8`, `s₂ = 49/100`. -/
theorem spineDatumCoarseGrainingRecutFlux_of_core_pinned [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ)
    (sb : {s : ℝ // 0 < s}) {sigmaBarM Kabs : ℝ} (hsig : 0 < sigmaBarM)
    (omega : Cutoff.CutoffSample d)
    (hcore : SpineDatumRecutCoreFlux M Cgap Y m sb sigmaBarM hsig Kabs
      (recutExponent d (le_trans (by norm_num) hd)) recutOrderTop omega) :
    SpineDatumCoarseGrainingRecutFlux M Cgap Y m sb sigmaBarM hsig Kabs omega := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨hlt, hgt⟩ := recutOrderTop_window d hd1
  exact spineDatumCoarseGrainingRecutFlux_of_core hd M Cgap Y m sb hsig
    (recutExponent d hd1) recutOrderTop (recutExponent_two_le d hd1) hlt hgt omega hcore

/-! ## 4. The residual bill -/

/-- **THE SUPPLIER, at the printed coefficient.**

What the §4.5 spine still needs, per `ω`: the energy partial-sum slot with the
Step-2 bound (the Theorem-C item), the multiscale coarse-graining clause at the
`ã` slots, and the ONE honest coefficient input
`HomSeamFluxCoefficient.FluxCorrectedParentIdentification`.

Compared with `HomSpineResidueCore.RecutCoreSupply` the two `𝓔`-dominations are
gone — they are produced below from the identification.

SIGMA PIN.  The
comparator is the printed `σ̄_m` itself, not a free scalar, because
`FluxCorrectedParentIdentification` is now typed at that pin (see
`HomSeamFluxCoefficient`).  The spine instantiates this chain only at
`Annealed.sigmaBar M m`, so nothing downstream moves. -/
def RecutCoreSupplyFlux [NeZero d] (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m : ℤ) (Cen0 : ℝ)
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
            (recutPinnedCcgFlux d (recutExponent d hd1)) (homS M) (homS M / 4)
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

/-! ## 5. THE PRODUCER -/

/-- **THE TWELVE-CONJUNCT `ã` CORE, PRODUCED.**

Everything `SpineDatumRecutCoreFlux` asks for, at the corrected numeral pin and
at the re-pinned base `s' = s/8`, from `RecutCoreSupplyFlux`, the a.e.
finiteness of `EthmB(m)` at that base, and the `K_abs` frame condition.

Composing with `spineDatumCoarseGrainingRecutFlux_of_core_pinned` and
`HomSeamFluxBundle.homSpineClauseSupplierAt_of_datumRecutFlux` carries it to the
spine's clause supplier at the base `s/8`. -/
theorem spineDatumRecutCoreFlux_of_supply [NeZero d] (hd1 : 1 ≤ d) (M : ABKModel d)
    {Cgap : ℝ} (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (hs : 0 < homS M)
    {Kabs Cen0 : ℝ}
    (omega : Cutoff.CutoffSample d) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hfin : ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega ≠ ⊤)
    (hKabs : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
        (recutPinnedCwFlux d hd1 M Cgap Cen0) (stepFourSchauderConstU d) ≤ Kabs)
    (hsupply : RecutCoreSupplyFlux M Y m Cen0 hd1 hlog omega) :
    SpineDatumRecutCoreFlux M Cgap Y m (homSeamBase M hs)
      ((Annealed.sigmaBar M m : ℝ)) (Annealed.sigmaBar M m).2 Kabs
      (recutExponent d hd1) recutOrderTop omega := by
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨S, Fflux, hS0, hS, hSbound, hCGm, hid⟩ :=
    hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  /- the data signs, from the root's own binde -/
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hcen : cubeCenter (originCube d m) ∈ openCubeSet (originCube d m) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  have hKhInf0 : (0 : ℝ) ≤ KhInf :=
    le_trans (norm_nonneg _) (hKhInf (cubeCenter (originCube d m)) hcen)
  /- the two dominations, from the ONE honest identificati -/
  have hdom1 := seamDom1Flux_of_identification M m (homK M) omega hs hlog hid L hL
  have hdom2 := seamDom2Flux_of_identification M m (homK M) omega hs hlog hid L hL
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
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcgFlux d (recutExponent d hd1) :=
    recutPinnedCcgFlux_nonneg d (recutExponent d hd1)
  have hCw0 : (0 : ℝ) ≤ recutPinnedCwFlux d hd1 M Cgap Cen0 := by
    have h1 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop
      (Ccg := recutPinnedCcgFlux d (recutExponent d hd1)) (Cgap := Cgap) (Cen0 := Cen0)
      (sbase := homS M) (kappa := 1) (theta := 1) hCcg0 hCgap hCen0 hs zero_le_one one_pos
      (by linarith only [hss2]) hCdata0 hgapexp
    have h2 := pairCwLegOf_nonneg d (recutExponent d hd1) recutOrderTop
      (Ccg := recutPinnedCcgFlux d (recutExponent d hd1)) (Cgap := Cgap) (Cen0 := Cen0)
      (sbase := homS M) (kappa := recutPinnedKtest d hd1 M) (theta := 7 / 8) hCcg0 hCgap
      hCen0 hs hKtest0 (by norm_num) (by linarith only [hss2, hs]) hCdata0 hgapexp
    rw [recutPinnedCwFlux, pairCwOf]
    linarith only [h1, h2]
  have hjn : (originCube d m).scale - ((homK M : ℕ) : ℤ) = homN M m := rfl
  refine ⟨homK M, recutPinnedCwFlux d hd1 M Cgap Cen0, S,
    (ethmB M Cgap Y m (homN M m) (homSeamBase M hs) omega).toReal, recutOrderBase M hlog,
    Fflux, homK_pos hlog, hguard, ?_, hCw0, hKabs, ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal_le, hCGm, hS0, hS, ?_, ?_⟩
  · simp only [recutOrderBase_val]
    linarith only [hss2, hs]
  · exact recutHlevelFlux_of_seam M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hs hlog hgamma1 hCgap hss2 hs2lt hs2gt hgapexp
      hKtest0 hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin
  · exact recutHlevelDualFlux_of_seam hd1 M L omega m (homK M) (Annealed.sigmaBar M m).2 Y
      (recutExponent d hd1) recutOrderTop hs hlog hgamma1 hCgap hguard hss2 hs2lt hs2gt
      hgapexp rfl hKg hKhInf0 hKh0 hCen0 hjn hSbound hdom1 hdom2 hfin

end

end Algsuperdiff.Section4.Provider.Homogenization
