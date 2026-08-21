/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomProviderBSeamResidue
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfSupply

/-!
# The conditional provider WITHOUT the `C_w` envelope hypothesis

## What this file removes

`HomProviderBSeamResidue.generator_renormalization_provider_final_of_energySupply`
carries two hypotheses beyond the numeral binders:

```text
  hCw0: ∀ hd M, recutPinnedCwFlux d _ M Cgap Cen0 ≤ Cw0      -- UNSATISFIABLE
  hsupply: the a.e. energy supply
```

The first is machine-measured to be unsatisfiable at the
`α = s` pin: `recutPinnedKtest = cgTestConstBase d (homS M) (7 homS M/8) p′`
carries the radial kernel's geometric factor at the order gap `s/8`, so it
diverges like `|log γ|^{1/p′}` and `recutPinnedCwFlux`, which is linear in it,
has no `M`-uniform bound.

At the print's own Schauder provenance `α = 1/2` (the re-cut) the same constant
is bounded by `recutKtestHalfBound d hd1`, which names `d` and `p′` only, so
`HomSeamFluxHalfPin.exists_recutCwHalf_envelope` DISCHARGES the hypothesis
outright.  This file threads that discharge to the root shape.

## The resulting hypothesis list

`generator_renormalization_provider_final_of_energySupplyHalf` asks for

```text
  0 < cstar, 0 < gamma0, 0 < Cgap, 0 ≤ Cen0, 0 ≤ Ctop     -- numeral binders
  hsupply: the a.e. energy supply at the seam base       -- the ONE residue
```

and nothing else.  `K_abs` is no longer a slot at all: it is the closed term
`recutKabsHalf d hd1 Cgap Cen0`, fixed before the model quantifier.

`Cen0` remains free.  Whether the energy-slot constant supplied for it is
itself model-uniform is a SEPARATE question, still open; nothing here asserts
that it is.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The seam bundle at the re-pinned gauge -/

/-- `HomProviderBSeamAssembly.SeamBundleOfRegularity` with the per-`ω` datum
taken at the Schauder gauge `α = 1/2`.  Every binder is verbatim. -/
def SeamBundleOfRegularityHalf (d : ℕ) [NeZero d] (cstar gamma0 Cgap Kabs Ctop : ℝ) :
    Prop :=
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
          SpineDatumCoarseGrainingRecutFluxHalf M Cgap
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
            (homSeamBase M hs) ((Annealed.sigmaBar M m : ℝ))
            (Annealed.sigmaBar M m).2 Kabs omega

/-! ## 2. The absorbed constant, closed -/

/-- **THE ABSORBED CONSTANT OF THE RE-CUT LANE, AS A CLOSED TERM.**

`HomSchauderUniform.spineClauseConst_le_abs`'s shape at the envelope, taken at
the lane's own pinned coarse-graining constant.  It names `d`, the printed
exponent `p = 4d`, `C_gap` and `C_en⁰` — no model. -/
def recutKabsHalf (d : ℕ) (hd1 : 1 ≤ d) (Cgap Cen0 : ℝ) : ℝ :=
  (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
    recutCwHalfEnvelope d hd1 (recutPinnedCcgFlux d (recutExponent d hd1)) Cgap Cen0

theorem recutKabsHalf_nonneg (d : ℕ) (hd1 : 1 ≤ d) {Cgap Cen0 : ℝ} (hCgap : 0 < Cgap)
    (hCen0 : 0 ≤ Cen0) : 0 ≤ recutKabsHalf d hd1 Cgap Cen0 := by
  have hU : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
  have hd2 : (0 : ℝ) ≤ 288 * (d : ℝ) ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hsq]
  exact mul_nonneg (by linarith only [hU, hd2])
    (recutCwHalfEnvelope_nonneg d hd1 (recutPinnedCcgFlux_nonneg d (recutExponent d hd1))
      hCgap hCen0)

/-! ## 3. THE REDUCTION, WITH `hCw0` DISCHARGED -/

/-- **THE SEAM RESIDUE, REDUCED TO THE ENERGY CONJUNCTS ALONE.**

`HomProviderBSeamResidue.seamBundleOfRegularity_of_energySupply` with the `C_w`
envelope hypothesis GONE: at the re-pinned gauge the envelope is a theorem
(`HomSeamFluxHalfPin.recutCwHalfFluxAt_le_envelope`), so the `K_abs` frame is
met by the closed term `recutKabsHalf d hd1 Cgap Cen0`. -/
theorem seamBundleOfRegularityHalf_of_energySupply (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    {cstar gamma0 Cgap Cen0 Ctop : ℝ} (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hsupply : SeamEnergySupplyOfRegularity d (le_trans (by norm_num) hd) cstar gamma0
      Cen0 Ctop) :
    SeamBundleOfRegularityHalf d cstar (min gamma0 (1 / 81)) Cgap
      (recutKabsHalf d (le_trans (by norm_num) hd) Cgap Cen0) Ctop := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcgFlux d (recutExponent d hd1) :=
    recutPinnedCcgFlux_nonneg d (recutExponent d hd1)
  have hCcgDom : cgDualBoundConstFlux d (recutExponent d hd1) ≤
      ENNReal.ofReal (recutPinnedCcgFlux d (recutExponent d hd1)) :=
    cgDualBoundConstFlux_le_ofReal_of_pinned_le d hd (recutExponent d hd1)
      (recutExponent_two_le d hd1) le_rfl
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
  /- the `K_abs` frame, met before the model and without an assumed envelope -/
  have hKabsC : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
      (recutCwHalfFluxAt d hd1 M (recutPinnedCcgFlux d (recutExponent d hd1)) Cgap Cen0)
      (stepFourSchauderConstU d) ≤ recutKabsHalf d hd1 Cgap Cen0 :=
    spineClauseConst_le_abs_half d hd1 M hCcg0 hCgap hCen0 hlog
  filter_upwards [hsupF, hfin] with omega hsupplyOmega hfinOmega
  exact spineDatumCoarseGrainingRecutFluxAtHalf_of_core_pinned hd M Cgap
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
    (homSeamBase M hs) (Annealed.sigmaBar M m).2 hCcg0 hCcgDom omega
    (spineDatumRecutCoreFluxAtHalf_of_supply hd1 M
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m hs hCcg0
      omega hlog hgamma1 hCgap hCen0 hfinOmega hKabsC hsupplyOmega)

/-! ## 4. The spine endpoint at the re-pinned bundle -/

/-- **THE SPINE, at `{htail, the re-pinned `ã` bundle at the printed base}`.**

`HomProviderBSeamClose.homogenization_spine_close_of_seamBundle` with the
per-`ω` datum taken at `α = 1/2`.  The statement differs in exactly that one
hypothesis; the proof differs in exactly one line — the supplier producer, which
delivers a BYTE-IDENTICAL `HomSpineClauseSupplierAt`. -/
theorem homogenization_spine_close_of_seamBundleHalf (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) {Cst Cgap Kabs Ctop : ℝ} (hCst : 1 ≤ Cst)
    (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) (hCtop : 0 ≤ Ctop) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
          (∀ N : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
              ENNReal.ofReal (Cst *
                Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
                  (Cst * M.gamma)))) →
          ∀ hs : 0 < homS M, ∀ m : ℤ,
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              SpineDatumCoarseGrainingRecutFluxHalf M Cgap
                (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
                (homSeamBase M hs) ((Annealed.sigmaBar M m : ℝ))
                (Annealed.sigmaBar M m).2 Kabs omega) →
            ∃ sigmaBar : ℝ, 0 < sigmaBar ∧
              |sigmaBar -
                  Real.sqrt (M.nu ^ (2 : ℕ) +
                    cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
                C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar ∧
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
                          (fun _ => sigmaBar • (1 : Mat d)) (originCube d m) v h g →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kg g →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kh h.grad →
                      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                      (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                        Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                          EB omega *
                            (sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                              (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                        |volumeAverage (openCubeSet (originCube d m))
                              (fun y => M.nu * vecNormSq (u.grad y)) -
                            volumeAverage (openCubeSet (originCube d m))
                              (fun y => sigmaBar * vecNormSq (v.grad y))| ≤
                          EB omega *
                            (Real.sqrt sigmaBar⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                                Real.sqrt sigmaBar *
                                  (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                              (2 : ℕ) := by
  obtain ⟨g1, C0, hg1, hC0, hdisp⟩ :=
    exists_ethmB_seam_moment_bound d cstar hcstar (Cgate := homGateRangeConst Cst)
      hCtop (homGateRangeConst_pos hCst)
  obtain ⟨g0, C, hg0, hC, hend⟩ :=
    homogenization_spine_close_of_stepOneDisplay d cstar hcstar (Cgap := Cgap)
      (Kabs := Kabs) (C0 := C0) hCgap hKabs hC0
  refine ⟨min g0 (min g1 (min (homGamma0Gate Cst) (1 / 81))), C,
    lt_min hg0 (lt_min hg1 (lt_min (homGamma0Gate_pos hCst) (by norm_num))), hC, ?_⟩
  intro M hcs hgamma X hX htail hs m hbundle
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_end : M.gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hg_disp : M.gamma ≤ g1 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg_gate : M.gamma ≤ homGamma0Gate Cst :=
    le_trans hgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hg_81 : M.gamma ≤ 1 / 81 :=
    le_trans hgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg_81
  /- the Theorem-C edge, at the gate consta -/
  have hY0 : ∀ p : ℝ, 1 ≤ p →
      p ≤ (homGateRangeConst Cst)⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ w, homMinimalScaleFactor (1 - homAlpha M) X w ^ (2 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal 2 ^ (2 * p) := by
    intro p hp hrange
    exact homY_moment_bound_of_gamma_le M hX hCst hp hL4 hg_gate hrange htail
  have hYmeas : Measurable
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) :=
    measurable_seamEnlargedY M m Ctop (measurable_homMinimalScaleFactor _ hX)
  refine hend M hcs hg_end
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) hYmeas m
    (homSeamBase M hs)
    (hdisp M hcs hg_disp hs m (homMinimalScaleFactor (1 - homAlpha M) X)
      (measurable_homMinimalScaleFactor _ hX).aemeasurable hY0 Cgap hCgap) ?_
  exact hbundle.mono fun omega hb =>
    homSpineClauseSupplierAt_of_datumRecutFluxHalf hd M Cgap
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
      (homSeamBase M hs) (Annealed.sigmaBar M m).2 omega hb

/-! ## 5. THE CONDITIONAL PROVIDER, AT THE ENERGY SUPPLY ALONE -/

/-- **The frozen `generator_renormalization` body from the re-pinned seam
bundle, at `2 ≤ d`.**

`HomProviderBSeamAssembly.generator_renormalization_provider_of_seamBundle` with
the bundle taken at `α = 1/2`. -/
theorem generator_renormalization_provider_of_seamBundleHalf (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) {gamma0res Cgap Kabs Ctop : ℝ}
    (hg0res : 0 < gamma0res) (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) (hCtop : 0 ≤ Ctop)
    (hcore : SeamBundleOfRegularityHalf d cstar gamma0res Cgap Kabs Ctop) :
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
    homogenization_spine_close_of_seamBundleHalf d hd cstar hcstar (Cst := Cst)
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

/-- **The frozen `generator_renormalization` body from the energy supply
alone.**

The hypothesis list is `{0 < cstar, 0 < gamma0, 0 < Cgap, 0 ≤ Cen0, 0 ≤ Ctop}`
plus the a.e. energy supply.  The `C_w` envelope hypothesis of
`HomProviderBSeamResidue.generator_renormalization_provider_final_of_energySupply`
— which is machine-measured to be UNSATISFIABLE at the `α = s` pin —
is DISCHARGED here, and `K_abs` is the closed term
`recutKabsHalf d hd1 Cgap Cen0`.

What remains of Theorem B's §4.5 lane is therefore exactly the a.e. energy
supply `{0 ≤ S, the partial-sum slot, hSbound, the multiscale coarse-graining
clause}`. -/
theorem generator_renormalization_provider_final_of_energySupplyHalf (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0 Cgap Cen0 Ctop : ℝ} (hg0 : 0 < gamma0)
    (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0) (hCtop : 0 ≤ Ctop)
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
  by_cases hd : 2 ≤ d
  · haveI inst : NeZero d := ⟨by omega⟩
    exact generator_renormalization_provider_of_seamBundleHalf d hd cstar hcstar
      (lt_min hg0 (by norm_num)) hCgap.le
      (recutKabsHalf_nonneg d (le_trans (by norm_num) hd) hCgap hCen0) hCtop
      (seamBundleOfRegularityHalf_of_energySupply d hd hCgap hCen0 (hsupply hd inst))
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma _m
    exact absurd M.shellPrefix.dimension hd

end

end Algsuperdiff.Section4.Provider.Homogenization
