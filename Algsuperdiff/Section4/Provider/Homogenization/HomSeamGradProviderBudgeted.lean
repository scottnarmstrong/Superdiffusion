/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamSpineBudget
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradProvider

/-!
# The budgeted conditional provider chain: `C_en⁰` and `K_abs` as model functions

## Why the two slots move inside the model quantifier

The finite-`p` energy factor `coarseGrainingGeomFactor (4d) (s/4)` is NOT
`γ`-uniform: at the §4.5 pin it is `≍ |log γ|^{1/(4d)}`
(`coarseGrainingGeomFactor_ge_inv_rpow`).  Fixing `C_en⁰` — and therefore
`K_abs` — BEFORE the model quantifier would therefore need a separate geometric
hypothesis `hgeom`.

That requirement is avoided here.  The two slots become FUNCTIONS of the
model, gated by ONE budget

```text
  K_abs(M) ≤ C_abs · |log γ_M|,
```

and the extra `|log γ|` of the display absorbs them
(`HomSeamSpineBudget.exists_spine_defect_witness_of_displayBudget`).  Everything
else in this file is the chain of `HomSeamGradProvider` with `C_en⁰`
replaced by `C_en⁰(M)` and `K_abs` by `K_abs(M)`; no proof step changes.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The two supply layers, at model-dependent slots -/

/-- `HomSeamGradProvider.SeamEnergySupplyOfRegularityGrad` with the energy-slot
constant `C_en⁰` a FUNCTION of the model.  Nothing else changes. -/
def SeamEnergySupplyOfRegularityGradBudget (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar gamma0 : ℝ) (Cen0F : ABKModel d → ℝ) (Ctop Creg : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ),
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RecutCoreSupplyFluxEnergyGrad M
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
            (Cen0F M) hd1 hlog omega

/-- `HomSeamGradProvider.SeamBundleOfRegularityHalfGrad` with the `K_abs` slot a
FUNCTION of the model. -/
def SeamBundleOfRegularityHalfGradBudget (d : ℕ) [NeZero d]
    (cstar gamma0 Cgap : ℝ) (KabsF : ABKModel d → ℝ) (Ctop Creg : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hs : 0 < homS M) (m : ℤ),
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          ethmB M Cgap
              (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
              (homN M m) (homSeamBase M hs) omega ≠ ⊤) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          SpineDatumCoarseGrainingRecutFluxHalfGrad M Cgap
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
            (homSeamBase M hs) ((Annealed.sigmaBar M m : ℝ))
            (Annealed.sigmaBar M m).2 (KabsF M) omega

/-! ## 2. The reduction, at the model-dependent slots -/

/-- `HomSeamGradProvider.seamBundleOfRegularityHalfGrad_of_energySupplyGrad` at
model-dependent slots.  `K_abs(M)` is still the CLOSED term
`recutKabsHalf d hd1 Cgap (C_en⁰(M))`; the proof is the same one applied at
each `M`. -/
theorem seamBundleOfRegularityHalfGradBudget_of_energySupplyGradBudget (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) {cstar gamma0 Cgap Ctop Creg : ℝ} {Cen0F : ABKModel d → ℝ}
    (hCgap : 0 < Cgap)
    (hCen0 : ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| → 0 ≤ Cen0F M)
    (hsupply : SeamEnergySupplyOfRegularityGradBudget d (le_trans (by norm_num) hd) cstar
      gamma0 Cen0F Ctop Creg) :
    SeamBundleOfRegularityHalfGradBudget d cstar (min gamma0 (1 / 81)) Cgap
      (fun M => recutKabsHalf d (le_trans (by norm_num) hd) Cgap (Cen0F M)) Ctop Creg := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hCcg0 : (0 : ℝ) ≤ recutPinnedCcgFlux d (recutExponent d hd1) :=
    recutPinnedCcgFlux_nonneg d (recutExponent d hd1)
  have hCcgDom : cgDualBoundConstFlux d (recutExponent d hd1) ≤
      ENNReal.ofReal (recutPinnedCcgFlux d (recutExponent d hd1)) :=
    cgDualBoundConstFlux_le_ofReal_of_pinned_le d hd (recutExponent d hd1)
      (recutExponent_two_le d hd1) le_rfl
  intro M hcs hgamma hs m X hXmeas hXfin hXdisp hfin
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_s : M.gamma ≤ gamma0 := le_trans hgamma (min_le_left _ _)
  have hg81 : M.gamma ≤ 1 / 81 := le_trans hgamma (min_le_right _ _)
  have hlog : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg81
  have hgamma1 : M.gamma < 1 := by linarith only [hg81]
  have hsupF := ae_recutCoreSupplyFluxAtGrad_of_energyGrad M
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m (Cen0F M) hd1 hlog
    (hsupply M hcs hg_s hlog m X hXmeas hXfin hXdisp)
  have hKabsC : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
      (recutCwHalfFluxAt d hd1 M (recutPinnedCcgFlux d (recutExponent d hd1)) Cgap (Cen0F M))
      (stepFourSchauderConstU d) ≤ recutKabsHalf d hd1 Cgap (Cen0F M) :=
    spineClauseConst_le_abs_half d hd1 M hCcg0 hCgap (hCen0 M hlog) hlog
  filter_upwards [hsupF, hfin] with omega hsupplyOmega hfinOmega
  exact spineDatumCoarseGrainingRecutFluxAtHalfGrad_of_core_pinned hd M Cgap
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
    (homSeamBase M hs) (Annealed.sigmaBar M m).2 hCcg0 hCcgDom omega
    (spineDatumRecutCoreFluxAtHalfGrad_of_supply hd1 M
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m hs hCcg0
      omega hlog hgamma1 hCgap (hCen0 M hlog) hfinOmega hKabsC hsupplyOmega)

/-! ## 3. The spine endpoint at the budgeted bundle -/

/-- `HomSeamGradProvider.homogenization_spine_close_of_seamBundleHalfGrad` at a
model-dependent `K_abs` gated by the budget, delivering the frozen
moment display at `|log γ|³`. -/
theorem homogenization_spine_close_of_seamBundleHalfGradBudget (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) {Cst Cgap Cabs Ctop : ℝ}
    {KabsF : ABKModel d → ℝ} (hCst : 1 ≤ Cst) (hCgap : 0 ≤ Cgap) (hCabs : 0 ≤ Cabs)
    (hKabs : ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| → 0 ≤ KabsF M)
    (hKbud : ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
      KabsF M ≤ Cabs * |Real.log M.gamma|) (hCtop : 0 ≤ Ctop) :
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
              SpineDatumCoarseGrainingRecutFluxHalfGrad M Cgap
                (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
                (homSeamBase M hs) ((Annealed.sigmaBar M m : ℝ))
                (Annealed.sigmaBar M m).2 (KabsF M) omega) →
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
                          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
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
                      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
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
    homogenization_spine_close_of_stepOneDisplayBudget d cstar hcstar (Cgap := Cgap)
      (Cabs := Cabs) (C0 := C0) hCgap hCabs hC0
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
  refine hend M hcs hg_end (KabsF M) (hKabs M hL4) (hKbud M hL4)
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) hYmeas m
    (homSeamBase M hs)
    (hdisp M hcs hg_disp hs m (homMinimalScaleFactor (1 - homAlpha M) X)
      (measurable_homMinimalScaleFactor _ hX).aemeasurable hY0 Cgap hCgap) ?_
  exact hbundle.mono fun omega hb =>
    homSpineClauseSupplierAtGrad_of_datumRecutFluxHalfGrad hd M Cgap
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
      (homSeamBase M hs) (Annealed.sigmaBar M m).2 omega hb

/-! ## 4. THE CONDITIONAL PROVIDER, at the budgeted bundle -/

/-- **THE FROZEN `generator_renormalization` BODY FROM THE BUDGETED SEAM
BUNDLE.**

`HomSeamGradProvider.generator_renormalization_provider_of_seamBundleHalfGrad`
with the `K_abs` slot a function of BOTH the hoisted Theorem-C constant `Creg`
and the model, gated by the single budget `K_abs(Creg, M) ≤ C_abs·|log γ|`.
The conclusion is the display factor `|Real.log M.gamma| ^ (3: ℕ)`. -/
theorem generator_renormalization_provider_of_seamBundleHalfGradBudget (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) {gamma0res Cgap Ctop : ℝ}
    {CabsF : ℝ → ℝ} {KabsF : ℝ → ABKModel d → ℝ} (hg0res : 0 < gamma0res)
    (hCgap : 0 ≤ Cgap) (hCabs : ∀ Creg : ℝ, 0 < Creg → 0 ≤ CabsF Creg)
    (hKabs : ∀ Creg : ℝ, 0 < Creg → ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
      0 ≤ KabsF Creg M)
    (hKbud : ∀ Creg : ℝ, 0 < Creg → ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
      KabsF Creg M ≤ CabsF Creg * |Real.log M.gamma|)
    (hCtop : 0 ≤ Ctop)
    (hcore : ∀ Creg : ℝ, 0 < Creg →
      SeamBundleOfRegularityHalfGradBudget d cstar gamma0res Cgap (KabsF Creg) Ctop Creg) :
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
                      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
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
    homogenization_spine_close_of_seamBundleHalfGradBudget d hd cstar hcstar (Cst := Cst)
      (Cgap := Cgap) (Cabs := CabsF Creg) (KabsF := KabsF Creg) (Ctop := Ctop) hCst hCgap
      (hCabs Creg hCreg) (hKabs Creg hCreg) (hKbud Creg hCreg) hCtop
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
      (hcore Creg hCreg M hcs hg_res hs m X hXmeas
        (ae_ne_top_of_regTail M hCst hs hXtail) hXdisp
        (hfin M hcs hg_fin X hXmeas hXtail hs m))
  refine ⟨sigmaBarM, hsig, hdiff, EB, hEB0, hEBmeas, hEBmom, ?_⟩
  filter_upwards [hEBae] with omega hom
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  exact hom L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad

end

end Algsuperdiff.Section4.Provider.Homogenization
