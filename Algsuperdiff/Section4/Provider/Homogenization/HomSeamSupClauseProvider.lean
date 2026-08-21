/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamSupClauseSpine
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamClauseGeomProviderBudgeted

/-!
# THE BUDGETED CONDITIONAL PROVIDER AT THE SUP-FORM CLAUSE

## The deliverable

```text
  generator_renormalization_provider_final_of_supClause
      -- {0 < cstar, 0 < gamma0, 0 < Cgap} + {hclause at the SUP shape}
```

The clause input is now the paper's own sup-over-depths multiscale clause
(`HomSpineSupFormClause.CoarseGrainingSupMultiscale`), i.e. exactly the object
`exists_coarseGrainingSupMultiscale_of_depthConverseOn` produces from the
single-depth grid/smooth-dual comparison.  The factor `D3` is
discharged here as in `HomSeamClauseGeomProviderBudgeted`; the geometric factor rides
inside `C_en⁰(M)` and is paid for by the frozen display's extra `|log γ|`.

`supClauseSupply_of_clauseSupply` is the REGRESSION certificate: the
`ℓ^p` clause supply still drives this provider, so the re-cut only forgets.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The spine endpoint at the sup-form bundle -/

/-- `HomSeamGradProviderBudgeted.homogenization_spine_close_of_seamBundleHalfGradBudget`
at the sup-form datum. -/
theorem homogenization_spine_close_of_supBundleBudget (d : ℕ) [NeZero d]
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
              SpineDatumCoarseGrainingRecutFluxHalfSupGrad M Cgap
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
    homSpineClauseSupplierAtGrad_of_datumRecutFluxHalfSupGrad hd M Cgap
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
      (homSeamBase M hs) (Annealed.sigmaBar M m).2 omega hb

/-! ## 2. The provider at the sup-form bundle -/

/-- `HomSeamGradProviderBudgeted.generator_renormalization_provider_of_seamBundleHalfGradBudget`
at the sup-form bundle. -/
theorem generator_renormalization_provider_of_supBundleBudget (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) {gamma0res Cgap Ctop : ℝ}
    {CabsF : ℝ → ℝ} {KabsF : ℝ → ABKModel d → ℝ} (hg0res : 0 < gamma0res)
    (hCgap : 0 ≤ Cgap) (hCabs : ∀ Creg : ℝ, 0 < Creg → 0 ≤ CabsF Creg)
    (hKabs : ∀ Creg : ℝ, 0 < Creg → ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
      0 ≤ KabsF Creg M)
    (hKbud : ∀ Creg : ℝ, 0 < Creg → ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
      KabsF Creg M ≤ CabsF Creg * |Real.log M.gamma|)
    (hCtop : 0 ≤ Ctop)
    (hcore : ∀ Creg : ℝ, 0 < Creg →
      SeamBundleOfRegularityHalfSupGradBudget d cstar gamma0res Cgap (KabsF Creg) Ctop
        Creg) :
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
    homogenization_spine_close_of_supBundleBudget d hd cstar hcstar (Cst := Cst)
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

/-! ## 3. The SUP-form clause supply -/

variable {d : ℕ}

/-- **THE SUP-FORM MULTISCALE CLAUSE OF THE `ã` SEAM, ALONE.**

`HomSeamClauseGeomProvider.RecutCoreSupplyFluxClause` at the print's own
sup-over-depths aggregation.  Every other character — the constants, the orders,
the exponent, the two parent-error slots, the overlap slot — is the
one. -/
def RecutCoreSupplyFluxSupClause [NeZero d] (M : ABKModel d) (m : ℤ)
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
      ∃ Fflux : Vec d → Vec d,
        ∀ G : Vec d → Vec d,
          (∀ x ∈ openCubeSet (originCube d m), G x = u.grad x - v.grad x) →
          CoarseGrainingSupMultiscale (originCube d m) (homK M)
            (recutPinnedCcgFlux d (recutExponent d hd1)) (homS M) (homS M / 4)
            (recutOrderTop : FractionalOrder).1 (recutExponent d hd1).exponent.toReal
            ((Annealed.sigmaBar M m : ℝ))
            (recutPinnedE1Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedE2Flux M L omega m (homK M) (Annealed.sigmaBar M m).2
              (recutOrderBase M hlog))
            (recutPinnedDg m recutOrderTop (recutExponent d hd1) g)
            (printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u)
            G Fflux

/-- The sup-form clause, asked almost surely at every admissible model and
scale. -/
def SeamMultiscaleSupClauseSupply (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar gamma0 : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ),
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        RecutCoreSupplyFluxSupClause M m hd1 hlog omega

/-- **THE REGRESSION CERTIFICATE.**  The `ℓ^p` clause supply implies the
sup-form supply at the same constants, so the re-cut only forgets. -/
theorem supClauseSupply_of_clauseSupply (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    {cstar gamma0 : ℝ} (h : SeamMultiscaleClauseSupply d hd1 cstar gamma0) :
    SeamMultiscaleSupClauseSupply d hd1 cstar gamma0 := by
  have hp : (0 : ℝ) < (recutExponent d hd1).exponent.toReal :=
    finiteLpExponent_toReal_pos (recutExponent d hd1)
  intro M hcs hgamma hlog m
  filter_upwards [h M hcs hgamma hlog m] with omega hcl
  intro L hL u v h' g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨Fflux, hCGm⟩ := hcl L hL u v h' g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  exact ⟨Fflux, fun G hG => (hCGm G hG).toSup hp (Annealed.sigmaBar M m).2.le⟩

/-! ## 4. The energy supply from the sup-form clause -/

/-- `HomSeamClauseGeomProviderBudgeted.seamEnergySupplyGradBudget_of_clause` at the
sup-form clause. -/
theorem seamEnergySupplyGradSupBudget_of_supClause (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) {gamma0in : ℝ} (hg0in : 0 < gamma0in)
    (hclause : SeamMultiscaleSupClauseSupply d hd1 cstar gamma0in) :
    ∃ gamma0 Ctop : ℝ, 0 < gamma0 ∧ 0 ≤ Ctop ∧
      ∀ Creg : ℝ, 0 < Creg →
        SeamEnergySupplyOfRegularityGradSupBudget d hd1 cstar gamma0
          (fun M => Creg * 729 *
            coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
              (homS M / 4))
          Ctop Creg := by
  obtain ⟨Cstep, hCstep, hslot⟩ := seamEnergySlot_of_regularityDisplayAt d hd1
  obtain ⟨g2, hg2, hcuts⟩ := ae_seam_quarter_errors_ne_top d cstar hcstar
  refine ⟨min gamma0in g2, seamTopScaleConst d Cstep, lt_min hg0in hg2,
    seamTopScaleConst_nonneg d hCstep.le, ?_⟩
  intro Creg hCreg M hcs hgamma hlog m X hXmeas hXfin hXdisp
  have hg_in : M.gamma ≤ gamma0in := le_trans hgamma (min_le_left _ _)
  have hg_2 : M.gamma ≤ g2 := le_trans hgamma (min_le_right _ _)
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hcutsM := hcuts M hcs hg_2 hs m
  have hclM := hclause M hcs hg_in hlog m
  have hrep1 := ae_forall_fluxCorrectedError_eq_representative M m
    ⟨1 / 4 / 2, half_pos seamQuarterPos⟩
  have hrep2 := ae_forall_fluxCorrectedError_eq_representative M m
    ⟨1 / 4, seamQuarterPos⟩
  filter_upwards [hXdisp, hXfin, hcutsM, hclM, hrep1, hrep2] with omega hdisp hXne hcut
    hcl hr1 hr2
  intro L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf hgrad
  obtain ⟨Fflux, hCGm⟩ := hcl L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hXne
  obtain ⟨S, hS0, hSpart, hSb⟩ :=
    hslot M m omega hCreg hlog hk.symm hdisp L hL u h g Kg Kh KhInf hsol hKg hKh hKhInf
      hgrad (hr1 ⟨L, hL⟩) (hr2 ⟨L, hL⟩) hcut.1 hcut.2.1 hcut.2.2
  refine ⟨S, Fflux, hS0, hSpart, ?_, hCGm⟩
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : (0 : ℝ) ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hcen : cubeCenter (originCube d m) ∈ openCubeSet (originCube d m) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  have hKhInf0 : (0 : ℝ) ≤ KhInf :=
    le_trans (norm_nonneg _) (hKhInf (cubeCenter (originCube d m)) hcen)
  have hB : (0 : ℝ) ≤ energyBracket ((Annealed.sigmaBar M m : ℝ))
      (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    energyBracket_nonneg (Real.rpow_nonneg (by norm_num) _) hKg0 hKhInf0 hKh0
  have hF : (0 : ℝ) ≤ recutEnergyFactor M
      (seamEnlargedY M m (seamTopScaleConst d Cstep)
        (homMinimalScaleFactor (1 - homAlpha M) X)) m omega :=
    recutEnergyFactor_nonneg _ _ _ _
  have hconst := recutEnergySlotConst_le_of_geom hd1 hCreg.le hlog
    (GEOM := coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
      (homS M / 4)) le_rfl
  exact le_trans hSb
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hF) hB)

/-! ## 5. THE CONDITIONAL PROVIDER AT THE SUP-FORM CLAUSE -/

/-- **THE FROZEN `generator_renormalization` BODY FROM THE SUP-FORM CLAUSE.**

`{0 < cstar, 0 < gamma0, 0 < Cgap}` plus the sup-form multiscale clause, and
NOTHING ELSE.  The factor `D3` is discharged inside. -/
theorem generator_renormalization_provider_final_of_supClause (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0 Cgap : ℝ} (hg0 : 0 < gamma0) (hCgap : 0 < Cgap)
    (hclause : ∀ (hd : 2 ≤ d) (inst : NeZero d),
      @SeamMultiscaleSupClauseSupply d inst (le_trans (by norm_num) hd) cstar gamma0) :
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
  by_cases hd : 2 ≤ d
  · haveI inst : NeZero d := ⟨by omega⟩
    have hd1 : 1 ≤ d := le_trans (by norm_num) hd
    obtain ⟨g1, Ctop, hg1, hCtop, hsupply⟩ :=
      seamEnergySupplyGradSupBudget_of_supClause d hd1 cstar hcstar hg0 (hclause hd inst)
    have hppos : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      rw [recutExponent_toReal]; linarith only [hdR]
    have hgeom0 : ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
        (0 : ℝ) ≤ coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
          (homS M / 4) := by
      intro M hlog
      have hs : 0 < homS M := homS_pos (by linarith only [hlog])
      exact coarseGrainingGeomFactor_nonneg hppos (by linarith only [hs])
    exact generator_renormalization_provider_of_supBundleBudget d hd cstar hcstar
      (CabsF := fun Creg => recutKabsHalf d hd1 Cgap 0 / 4 +
        |recutKabsHalf d hd1 Cgap 1 - recutKabsHalf d hd1 Cgap 0| * (Creg * 729 * 2))
      (KabsF := fun Creg M => recutKabsHalf d hd1 Cgap
        (Creg * 729 *
          coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4)))
      (lt_min hg1 (by norm_num)) hCgap.le
      (fun Creg hCreg => by
        have hb : (0 : ℝ) ≤ recutKabsHalf d hd1 Cgap 0 :=
          recutKabsHalf_nonneg d hd1 hCgap le_rfl
        have habs : (0 : ℝ) ≤
            |recutKabsHalf d hd1 Cgap 1 - recutKabsHalf d hd1 Cgap 0| * (Creg * 729 * 2) :=
          mul_nonneg (abs_nonneg _) (by linarith only [hCreg])
        linarith only [hb, habs])
      (fun Creg hCreg M hlog =>
        recutKabsHalf_nonneg d hd1 hCgap
          (mul_nonneg (by linarith only [hCreg]) (hgeom0 M hlog)))
      (fun Creg hCreg M hlog =>
        recutKabsHalf_le_budget d hd1 hCgap hCreg (hgeom0 M hlog)
          (recut_geomFactor_le_absLog hd1 M hlog) hlog)
      hCtop
      (fun Creg hCreg =>
        seamBundleOfRegularityHalfSupGradBudget_of_energySupplyGradSupBudget d hd hCgap
          (fun M hlog => mul_nonneg (by linarith only [hCreg]) (hgeom0 M hlog))
          (hsupply Creg hCreg))
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma _m
    exact absurd M.shellPrefix.dimension hd

end

end Algsuperdiff.Section4.Provider.Homogenization
