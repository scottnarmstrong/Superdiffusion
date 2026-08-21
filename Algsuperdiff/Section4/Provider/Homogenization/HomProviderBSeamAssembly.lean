/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomProviderBSeamClose
import Algsuperdiff.Section4.Provider.Homogenization.HomProviderBAssembly

/-!
# Theorem B, §4.5: the Theorem-B provider at the SEAM base

## What this file supplies

`HomProviderBAssembly.generator_renormalization_provider_final_of_core` is the
frozen body at the earlier core (`SpineDatumRecutCore` at the printed base,
the `a_L` lane).  That lane is replaced here by the print-accurate `ã` lane,
and the base and the `Y` slot have moved; the
core the chain now produces is
`HomSeamFluxBundle.SpineDatumCoarseGrainingRecutFlux` at
`(homSeamBase M hs, seamEnlargedY M m C_top ·)`.

This file is that assembly: the frozen body from Theorem C and ONE named
residue `SeamBundleOfRegularity`, plus the degenerate-`d` wrapper that restores
the frozen root's own binder prefix.

## The residue, named exactly

`SeamBundleOfRegularity` is: *given the Theorem-C display at `α = homAlpha M`
and its minimal scale `X`, the `ã` bundle holds a.e. at the seam base and the
enlarged `Y`.*  By
`HomSeamFluxCoreSupply.spineDatumCoarseGrainingRecutFlux_of_core_pinned` and
`spineDatumRecutCoreFlux_of_supply` what that still asks for is
`RecutCoreSupplyFlux` (the energy slot `hSbound`, the multiscale
coarse-graining clause, and —  — nothing else), together with `hfin` and the
`K_abs` frame condition.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. THE RESIDUE -/

/-- **THE ONE REMAINING OBLIGATION OF THEOREM B, at the `ã` lane.**

*From the Theorem-C display at the §4.5 web, the `ã` bundle at the seam
base `s/8` and the enlarged `Y` slot.*

THIS IS A HYPOTHESIS.  It is not proved in this file. -/
def SeamBundleOfRegularity (d : ℕ) [NeZero d] (cstar gamma0 Cgap Kabs Ctop : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hs : 0 < homS M) (m : ℤ) (Creg : ℝ), 0 < Creg →
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          ethmB M Cgap
              (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
              (homN M m) (homSeamBase M hs) omega ≠ ⊤) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          SpineDatumCoarseGrainingRecutFlux M Cgap
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
            (homSeamBase M hs) ((Annealed.sigmaBar M m : ℝ))
            (Annealed.sigmaBar M m).2 Kabs omega

/-! ## 2. THE PROVIDER -/

/-- **The frozen `generator_renormalization` body, at `2 ≤ d`, on the `ã`
lane.**

Byte-transcribed from the frozen statement, proved from
`HomProviderBSeamClose.homogenization_spine_close_of_seamBundle`,
`HomProviderBAssembly.exists_regularity_minimalScale`, and the residue.  The
frozen root's extra `HasGradientOn` binder is introduced and
discarded: the spine endpoint proves the display without it. -/
theorem generator_renormalization_provider_of_seamBundle (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) {gamma0res Cgap Kabs Ctop : ℝ}
    (hg0res : 0 < gamma0res) (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) (hCtop : 0 ≤ Ctop)
    (hcore : SeamBundleOfRegularity d cstar gamma0res Cgap Kabs Ctop) :
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
  obtain ⟨Cst, Creg, g1, hCst, hCreg, hg1, hreg⟩ :=
    exists_regularity_minimalScale d cstar hcstar
  obtain ⟨g0, C, hg0, hC, hend⟩ :=
    homogenization_spine_close_of_seamBundle d hd cstar hcstar (Cst := Cst)
      (Cgap := Cgap) (Kabs := Kabs) (Ctop := Ctop) hCst hCgap hKabs hCtop
  obtain ⟨g2, hg2, hfin⟩ :=
    ae_ethmB_seam_ne_top d cstar hcstar (Cst := Cst) (Cgap := Cgap) (Ctop := Ctop)
      hCst hCgap hCtop
  refine ⟨min g0 (min g1 (min g2 (min gamma0res (1 / 81)))), C,
    lt_min hg0 (lt_min hg1 (lt_min hg2 (lt_min hg0res (by norm_num)))), hC, ?_⟩
  intro M hcs hgamma m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_end : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hg_reg : M.gamma ≤ g1 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg_fin : M.gamma ≤ g2 :=
    le_trans hgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hg_res : M.gamma ≤ gamma0res :=
    le_trans hgamma
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hg_81 : M.gamma ≤ 1 / 81 :=
    le_trans hgamma
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg_81
  have hs : 0 < homS M := homS_pos (by linarith only [hL4])
  obtain ⟨X, hXmeas, hXtail, hXdisp⟩ := hreg M hcs hg_reg m
  obtain ⟨sigmaBarM, hsig, hdiff, EB, hEB0, hEBmeas, hEBmom, hEBae⟩ :=
    hend M hcs hg_end X hXmeas hXtail hs m
      (hcore M hcs hg_res hs m Creg hCreg X hXmeas hXdisp
        (hfin M hcs hg_fin X hXmeas hXtail hs m))
  refine ⟨sigmaBarM, hsig, hdiff, EB, hEB0, hEBmeas, hEBmom, ?_⟩
  filter_upwards [hEBae] with omega hom
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf _hgrad
  exact hom L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf

/-- **The frozen `generator_renormalization` body at the frozen prefix.**

The degenerate-`d` wrapper: `ABKModel d` already forces `2 ≤ d`
(`ShellLawPrefix.dimension`), so the low-dimensional branch is vacuous — the
same honest wrapper used for Theorem C. -/
theorem generator_renormalization_provider_final_of_seamBundle (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0res Cgap Kabs Ctop : ℝ} (hg0res : 0 < gamma0res)
    (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) (hCtop : 0 ≤ Ctop)
    (hcore : ∀ (_hd : 2 ≤ d) (inst : NeZero d),
      @SeamBundleOfRegularity d inst cstar gamma0res Cgap Kabs Ctop) :
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
  by_cases hd : 2 ≤ d
  · haveI inst : NeZero d := ⟨by omega⟩
    exact generator_renormalization_provider_of_seamBundle d hd cstar hcstar hg0res hCgap
      hKabs hCtop (hcore hd inst)
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma _m
    exact absurd M.shellPrefix.dimension hd

end

end Algsuperdiff.Section4.Provider.Homogenization
