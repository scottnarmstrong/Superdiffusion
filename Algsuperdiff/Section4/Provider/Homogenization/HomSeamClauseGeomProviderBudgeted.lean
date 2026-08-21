/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradProviderBudgeted
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamClauseGeomProvider
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamBudgetArith

/-!
# The budgeted conditional provider: `D3` discharged, the clause the only input

## What the extra logarithm buys

Under the earlier display the §4.5 lane needed a model-uniform bound `GEOM` for
the finite-`p` energy factor `coarseGrainingGeomFactor (4d) (s/4)`.  No such
bound exists (`HomSpineSupFormClause.coarseGrainingGeomFactor_ge_inv_rpow`: the
factor is `≍ |log γ|^{1/(4d)}`), so `HomSeamClauseGeomProvider` had to carry it
as the hypothesis `hgeom`.

The current display has one more `|log γ|` and the budget arithmetic
(`HomSeamBudgetArith.recut_geomFactor_le_absLog`) proves
`GEOM ≤ 2·|log γ|` outright.  So `hgeom` is DISCHARGED, not assumed:

```text
  generator_renormalization_provider_final_of_clause
      -- {0 < cstar, 0 < gamma0, 0 < Cgap} + {hclause}, and NOTHING ELSE
```

`C_en⁰(M) = Creg · 729 · GEOM(M)` and `K_abs(M) = recutKabsHalf d hd1 C_gap
(C_en⁰(M))` are closed terms pinned inside the proof; the `K_abs` budget is met
because `recutKabsHalf` is AFFINE in `C_en⁰` with model-free coefficients
(`recutKabsHalf_affine`).
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. `K_abs` is AFFINE in `C_en⁰`, with model-free coefficients -/

/-- **`recutKabsHalf` IS AFFINE IN `C_en⁰`.**

Both `recutKabsHalf` and `recutCwHalfEnvelope` are polynomial of degree one in
the energy-slot constant, so the whole `K_abs` frame is determined by its two
values at `C_en⁰ = 0` and `C_en⁰ = 1` — and neither of those mentions the
model.  This is what lets a MODEL-DEPENDENT `C_en⁰` still meet a model-free
budget. -/
theorem recutKabsHalf_affine (d : ℕ) (hd1 : 1 ≤ d) (Cgap Cen0 : ℝ) :
    recutKabsHalf d hd1 Cgap Cen0 =
      recutKabsHalf d hd1 Cgap 0 +
        (recutKabsHalf d hd1 Cgap 1 - recutKabsHalf d hd1 Cgap 0) * Cen0 := by
  rw [recutKabsHalf, recutKabsHalf, recutKabsHalf, recutCwHalfEnvelope,
    recutCwHalfEnvelope, recutCwHalfEnvelope]
  ring

/-- **THE `K_abs` BUDGET.**  If the energy factor is inside `2·L` then the whole
`K_abs` frame is inside `C_abs·L` at the model-free constant
`C_abs = K_abs(0)/4 + |slope| · 1458 · Creg`.  The `/4` is the printed gate
`4 ≤ L`: a constant is itself inside the budget. -/
theorem recutKabsHalf_le_budget (d : ℕ) (hd1 : 1 ≤ d) {Cgap : ℝ} (hCgap : 0 < Cgap)
    {Creg GEOM L : ℝ} (hCreg : 0 < Creg) (hGEOM0 : 0 ≤ GEOM) (hGEOM : GEOM ≤ 2 * L)
    (hL : 4 ≤ L) :
    recutKabsHalf d hd1 Cgap (Creg * 729 * GEOM) ≤
      (recutKabsHalf d hd1 Cgap 0 / 4 +
        |recutKabsHalf d hd1 Cgap 1 - recutKabsHalf d hd1 Cgap 0| *
          (Creg * 729 * 2)) * L := by
  have hb : (0 : ℝ) ≤ recutKabsHalf d hd1 Cgap 0 :=
    recutKabsHalf_nonneg d hd1 hCgap le_rfl
  set b : ℝ := recutKabsHalf d hd1 Cgap 0 with hbdef
  set a : ℝ := recutKabsHalf d hd1 Cgap 1 - recutKabsHalf d hd1 Cgap 0 with hadef
  have hC7 : (0 : ℝ) < Creg * 729 := by linarith only [hCreg]
  have hX0 : (0 : ℝ) ≤ Creg * 729 * GEOM := mul_nonneg hC7.le hGEOM0
  have haX : a * (Creg * 729 * GEOM) ≤ |a| * (Creg * 729 * GEOM) :=
    mul_le_mul_of_nonneg_right (le_abs_self a) hX0
  have hmono : |a| * (Creg * 729 * GEOM) ≤ |a| * (Creg * 729 * (2 * L)) := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    exact mul_le_mul_of_nonneg_left hGEOM hC7.le
  have hbL : b ≤ b / 4 * L := by
    have h := mul_le_mul_of_nonneg_left hL (by linarith only [hb] : (0 : ℝ) ≤ b / 4)
    linarith only [h]
  have haff := recutKabsHalf_affine d hd1 Cgap (Creg * 729 * GEOM)
  rw [← hbdef, ← hadef] at haff
  rw [haff]
  have hfin : b / 4 * L + |a| * (Creg * 729 * (2 * L)) =
      (b / 4 + |a| * (Creg * 729 * 2)) * L := by ring
  linarith only [haX, hmono, hbL, hfin.le, hfin.ge]

/-! ## 2. The energy supply at the model-dependent `C_en⁰`, from the clause alone -/

/-- **THE ENERGY SUPPLY OF THEOREM B'S §4.5 LANE, FROM THE CLAUSE ALONE.**

`HomSeamClauseGeomProvider.seamEnergySupplyGrad_of_clause_and_geom` with the
`hgeom` input REMOVED: the geometric factor is now carried in the slot itself,
`C_en⁰(M) = Creg · 729 · coarseGrainingGeomFactor (4d) (homS M / 4)`, and
nothing about its size is assumed here. -/
theorem seamEnergySupplyGradBudget_of_clause (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) {gamma0in : ℝ} (hg0in : 0 < gamma0in)
    (hclause : SeamMultiscaleClauseSupply d hd1 cstar gamma0in) :
    ∃ gamma0 Ctop : ℝ, 0 < gamma0 ∧ 0 ≤ Ctop ∧
      ∀ Creg : ℝ, 0 < Creg →
        SeamEnergySupplyOfRegularityGradBudget d hd1 cstar gamma0
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

/-! ## 3. THE CONDITIONAL PROVIDER -/

/-- **THE FROZEN `generator_renormalization` BODY FROM THE CLAUSE ALONE.**

The hypothesis list is `{0 < cstar, 0 < gamma0, 0 < Cgap}` plus the multiscale
coarse-graining clause, and NOTHING ELSE.  In particular the geometric
hypothesis `hgeom` is DISCHARGED here off the
budget (`HomSeamBudgetArith.recut_geomFactor_le_absLog`), and the extra
`|log γ|` of the display pays for it. -/
theorem generator_renormalization_provider_final_of_clause (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0 Cgap : ℝ} (hg0 : 0 < gamma0) (hCgap : 0 < Cgap)
    (hclause : ∀ (hd : 2 ≤ d) (inst : NeZero d),
      @SeamMultiscaleClauseSupply d inst (le_trans (by norm_num) hd) cstar gamma0) :
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
      seamEnergySupplyGradBudget_of_clause d hd1 cstar hcstar hg0 (hclause hd inst)
    have hppos : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      rw [recutExponent_toReal]; linarith only [hdR]
    have hgeom0 : ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
        (0 : ℝ) ≤ coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
          (homS M / 4) := by
      intro M hlog
      have hs : 0 < homS M := homS_pos (by linarith only [hlog])
      exact coarseGrainingGeomFactor_nonneg hppos (by linarith only [hs])
    exact generator_renormalization_provider_of_seamBundleHalfGradBudget d hd cstar hcstar
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
        seamBundleOfRegularityHalfGradBudget_of_energySupplyGradBudget d hd hCgap
          (fun M hlog => mul_nonneg (by linarith only [hCreg]) (hgeom0 M hlog))
          (hsupply Creg hCreg))
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma _m
    exact absurd M.shellPrefix.dimension hd

end

end Algsuperdiff.Section4.Provider.Homogenization
