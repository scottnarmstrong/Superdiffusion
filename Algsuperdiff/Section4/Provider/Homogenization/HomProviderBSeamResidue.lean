/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomProviderBSeamAssembly
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxIdentification

/-!
# Theorem B, §4.5: the seam residue reduced to the ENERGY conjuncts

## What this file supplies

`HomProviderBSeamAssembly.SeamBundleOfRegularity` — the ONE residue of the
Theorem-B provider — reduced to

```text
  SeamEnergySupplyOfRegularity:  ∀ᵐ ω, RecutCoreSupplyFluxEnergy … ω,
```

i.e. The energy residue (`hS0`, `hS`, `hSbound`, the multiscale coarse-graining
clause) at the seam base and the enlarged `Y`, plus ONE envelope for
the pairing constant.

The chain is: `HomSeamFluxIdentification.ae_recutCoreSupplyFlux_of_energy` (the
a.e. coefficient input, no hypotheses) →
`HomSeamFluxCoreSupply.spineDatumRecutCoreFlux_of_supply` →
`spineDatumCoarseGrainingRecutFlux_of_core_pinned`.  The `hfin` slot is the
assembly's own (`HomProviderBSeamClose.ae_ethmB_seam_ne_top`), threaded through
the residue's binders; the `K_abs` slot is the model-free
`HomSchauderUniform.spineClauseConst_le_abs`.

## The ONE input beyond the energy conjuncts

`hCw0` — a MODEL-UNIFORM envelope `C_w⁰` for the pairing constant
`recutPinnedCwFlux d hd1 M C_gap C_en⁰`, i.e. the `γ`-uniformity of `K_abs`:
`pairCwOf` is built from `Ccg`, `C_gap`, `C_en⁰`, `s = |log γ|⁻¹` and the
test-class constant, and only the `s`-dependence is model-dependent.  It is
carried here as a hypothesis, not assumed away, and it is a scalar inequality
in `γ` — no analytic content.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The energy residue, named -/

/-- **THE ENERGY RESIDUE OF THEOREM B**, at the seam base and the enlarged `Y`.

Exactly the `RecutCoreSupplyFluxEnergy` — `0 ≤ S`, the partial-sum slot,
`hSbound`, and the multiscale coarse-graining clause — asked for a.e., under
the Theorem-C display. -/
def SeamEnergySupplyOfRegularity (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar gamma0 Cen0 Ctop : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ) (Creg : ℝ), 0 < Creg →
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RecutCoreSupplyFluxEnergy M
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m Cen0
            hd1 hlog omega

/-! ## 2. The `C_w` positivity, at the pinned frame -/

/-- The pinned pairing constant of the `ã` chain is nonnegative.  This is the
block `HomSeamFluxCoreSupply.spineDatumRecutCoreFlux_of_supply` runs internally,
isolated so that the `K_abs` frame can be met before the model. -/
theorem recutPinnedCwFlux_nonneg {d : ℕ} (hd1 : 1 ≤ d) (M : ABKModel d) {Cgap Cen0 : ℝ}
    (hs : 0 < homS M) (hlog : 4 ≤ |Real.log M.gamma|) (hCgap : 0 < Cgap)
    (hCen0 : 0 ≤ Cen0) : 0 ≤ recutPinnedCwFlux d hd1 M Cgap Cen0 := by
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
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcgFlux d (recutExponent d hd1) :=
    recutPinnedCcgFlux_nonneg d (recutExponent d hd1)
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

/-! ## 3. THE REDUCTION -/

/-- **The seam residue, reduced to the energy conjuncts.**

`SeamBundleOfRegularity` — the one residue of
`HomProviderBSeamAssembly.generator_renormalization_provider_of_seamBundle` —
from the a.e. energy supply, the unconditional coefficient input, and the
`C_w` envelope.  The absorbed constant is the model-free `K_abs =
(2·stepFourSchauderConstU d + 288 d²)·C_w⁰`. -/
theorem seamBundleOfRegularity_of_energySupply (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    {cstar gamma0 Cgap Cen0 Ctop Cw0 : ℝ} (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hCw0 : ∀ M : ABKModel d,
      recutPinnedCwFlux d (le_trans (by norm_num) hd) M Cgap Cen0 ≤ Cw0)
    (hsupply : SeamEnergySupplyOfRegularity d (le_trans (by norm_num) hd) cstar gamma0
      Cen0 Ctop) :
    SeamBundleOfRegularity d cstar (min gamma0 (1 / 81)) Cgap
      ((2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) * Cw0) Ctop := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  intro M hcs hgamma hs m Creg hCreg X hXmeas hXdisp hfin
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_s : M.gamma ≤ gamma0 := le_trans hgamma (min_le_left _ _)
  have hg81 : M.gamma ≤ 1 / 81 := le_trans hgamma (min_le_right _ _)
  have hlog : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg81
  have hgamma1 : M.gamma < 1 := by linarith only [hg81]
  /- the coefficient input is unconditional, so the energy residue is the supp -/
  have hsupF := ae_recutCoreSupplyFlux_of_energy M
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m Cen0 hd1 hlog
    (hsupply M hcs hg_s hlog m Creg hCreg X hXmeas hXdisp)
  /- the `K_abs` frame, met before the mod -/
  have hquarter : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hquot : (d : ℝ) / (recutExponent d hd1).exponent.toReal = 1 / 4 :=
    recutExponent_quotient d hd1
  have hguard : homS M + (d : ℝ) / (recutExponent d hd1).exponent.toReal ≤ 1 / 2 := by
    rw [hquot]; linarith only [hquarter]
  have hKabsC : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
      (recutPinnedCwFlux d hd1 M Cgap Cen0) (stepFourSchauderConstU d) ≤
      (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) * Cw0 :=
    spineClauseConst_le_abs d (recutPinnedCwFlux_nonneg hd1 M hs hlog hCgap hCen0)
      (hCw0 M) hguard
  filter_upwards [hsupF, hfin] with omega hsupplyOmega hfinOmega
  exact spineDatumCoarseGrainingRecutFlux_of_core_pinned hd M Cgap
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
    (homSeamBase M hs) (Annealed.sigmaBar M m).2 omega
    (spineDatumRecutCoreFlux_of_supply hd1 M
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m hs omega
      hlog hgamma1 hCgap hCen0 hfinOmega hKabsC hsupplyOmega)

/-! ## 4. THE CONDITIONAL PROVIDER -/

/-- **The frozen `generator_renormalization` body from the energy supply.**

The composition of `generator_renormalization_provider_final_of_seamBundle` with
`seamBundleOfRegularity_of_energySupply`, at the frozen root's own binder
prefix.  What remains is exactly

```text
  { the a.e. energy supply at the seam base,  the C_w envelope },
```

and the energy supply is `{0 ≤ S, the partial-sum slot, hSbound, the multiscale
coarse-graining clause}` — the last of which is the
`exists_coarseGrainingFinitePMultiscale_of_testFamily` modulo the single open
construction `GridDualTestFamily`. -/
theorem generator_renormalization_provider_final_of_energySupply (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0 Cgap Cen0 Ctop Cw0 : ℝ} (hg0 : 0 < gamma0)
    (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) (hCtop : 0 ≤ Ctop) (hCw00 : 0 ≤ Cw0)
    (hCw0 : ∀ (hd : 2 ≤ d) (M : ABKModel d),
      recutPinnedCwFlux d (le_trans (by norm_num) hd) M Cgap Cen0 ≤ Cw0)
    (hsupply : ∀ (hd : 2 ≤ d) (inst : NeZero d),
      @SeamEnergySupplyOfRegularity d inst (le_trans (by norm_num) hd) cstar gamma0
        Cen0 Ctop) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
          |sigmaBarM -
              Real.sqrt (M.nu ^ (2 : ℕ) +
                cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
          ∃ EB : Cutoff.CutoffSample d → ℝ,
            (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal
                    (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                      Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ L : ℤ, m ≤ L →
                ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                  IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u h g →
                  IsDirichletSolutionOn
                      (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
                  HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
                  HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
                  (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                  HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
                  (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                      Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                        EB omega *
                          (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                    |volumeAverage (openCubeSet (originCube d m))
                          (fun y => M.nu * vecNormSq (u.grad y)) -
                        volumeAverage (openCubeSet (originCube d m))
                          (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
                      EB omega *
                        (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                            Real.sqrt sigmaBarM *
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                          (2 : ℕ) := by
  have hKabs0 : (0 : ℝ) ≤
      (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) * Cw0 := by
    have hU : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
    have hd2 : (0 : ℝ) ≤ 288 * (d : ℝ) ^ (2 : ℕ) := by positivity
    exact mul_nonneg (by linarith only [hU, hd2]) hCw00
  refine generator_renormalization_provider_final_of_seamBundle d cstar hcstar
    (gamma0res := min gamma0 (1 / 81)) (lt_min hg0 (by norm_num)) hCgap.le hKabs0 hCtop ?_
  intro hd inst
  exact @seamBundleOfRegularity_of_energySupply d inst hd cstar gamma0 Cgap Cen0 Ctop Cw0
    hCgap hCen0 (hCw0 hd) (hsupply hd inst)

end

end Algsuperdiff.Section4.Provider.Homogenization
