/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradProvider
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamEnergyFinitenessCuts

/-!
# The §4.5 conditional provider at the multiscale clause and the factor D3

## What this file supplies

`generator_renormalization_provider_final_of_clause_and_geom` reproduces the
frozen root's conclusion verbatim from EXACTLY

```text
  {0 < cstar, 0 < gamma0, 0 < Cgap, 0 ≤ GEOM}        -- numeral binders
  hclause: the multiscale coarse-graining clause, a.e., at the shape
  hgeom: one model-uniform bound for coarseGrainingGeomFactor (4d) (s/4)
```

and nothing else.  `C_en⁰`, `K_abs` and `C_top` are no longer slots: they are the
closed terms `Creg · 729 · GEOM`, `recutKabsHalf d hd1 Cgap (Creg · 729 · GEOM)`
and `seamTopScaleConst d C_step`, pinned INSIDE the proof after
`exists_regularity_minimalScale` has produced the model-free `Creg`.

`hgeom` is item **D3** and nothing else: it is exhibited as a hypothesis, not
assumed away.  Nothing here asserts that it holds.
-/

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The multiscale clause, named as the ONE analytic input -/

/-- **THE MULTISCALE COARSE-GRAINING CLAUSE OF THE `ã` SEAM, ALONE.**

The fourth conjunct of `HomSeamGradChain.RecutCoreSupplyFluxEnergyGrad`, at the
`ℓ^p` shape and the pins, with the three energy conjuncts removed. Every
character of the clause is unchanged: the coarse-graining constant is the lane's
own `recutPinnedCcgFlux d (recutExponent d hd1)`, the orders are `s = homS M`,
`s₁ = s/4`, `s₂ = recutOrderTop`, the exponent is `p = 4d`, and the two
parent-error slots and the overlap slot are the pinned ones.

Nothing here commits to a `sup`-over-cells or a per-cell reading: the shape is
byte-identical to the conjunct, and the reading is the manuscript's. -/
def RecutCoreSupplyFluxClause [NeZero d] (M : ABKModel d) (m : ℤ)
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
            G Fflux

/-- The clause, asked almost surely at every admissible model and scale. -/
def SeamMultiscaleClauseSupply (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar gamma0 : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ),
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        RecutCoreSupplyFluxClause M m hd1 hlog omega

/-! ## 2. The `Creg` hoist: `C_en⁰` split into `Creg`, a numeral, and D3 -/

/-- **THE `3^{(1-α)k}` FACTOR OF `recutEnergySlotConst` IS MODEL-FREE.**

`1 - α = s/2 = 1/(2|log γ|)` and `k = ⌈10|log γ|⌉ ≤ 10|log γ| + 1`, so the
exponent is at most `5 + 1/(2|log γ|) ≤ 41/8 ≤ 6` on the printed gate
`|log γ| ≥ 4`.  This is the half of `C_en⁰` that carries no `γ`. -/
theorem three_rpow_homAlpha_homK_le (M : ABKModel d)
    (hlog : 4 ≤ |Real.log M.gamma|) :
    (3 : ℝ) ^ ((1 - homAlpha M) * (homK M : ℝ)) ≤ 729 := by
  have htpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hlog]
  have hsplit : (1 : ℝ) - homAlpha M = homS M / 2 := by rw [homAlpha]; ring
  have hsval : homS M = |Real.log M.gamma|⁻¹ := rfl
  have hKnn : (0 : ℝ) ≤ (homK M : ℝ) := Nat.cast_nonneg _
  have hK := homK_le M
  have htinv : |Real.log M.gamma|⁻¹ ≤ 1 / 4 := by
    have hmul : |Real.log M.gamma|⁻¹ * (4 : ℝ) ≤
        |Real.log M.gamma|⁻¹ * |Real.log M.gamma| :=
      mul_le_mul_of_nonneg_left hlog (inv_pos.mpr htpos).le
    rw [inv_mul_cancel₀ (ne_of_gt htpos)] at hmul
    linarith only [hmul]
  have hfac : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ / 2 := by positivity
  have hprod : |Real.log M.gamma|⁻¹ / 2 * (homK M : ℝ) ≤
      |Real.log M.gamma|⁻¹ / 2 * (10 * |Real.log M.gamma| + 1) :=
    mul_le_mul_of_nonneg_left hK hfac
  have hexpand : |Real.log M.gamma|⁻¹ / 2 * (10 * |Real.log M.gamma| + 1) =
      5 + |Real.log M.gamma|⁻¹ / 2 := by
    field_simp
    ring
  have hexp : (1 - homAlpha M) * (homK M : ℝ) ≤ 6 := by
    rw [hsplit, hsval]
    rw [hexpand] at hprod
    linarith only [hprod, htinv]
  have hmono : (3 : ℝ) ^ ((1 - homAlpha M) * (homK M : ℝ)) ≤ (3 : ℝ) ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hval : (3 : ℝ) ^ (6 : ℝ) = 729 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [hval] at hmono
  exact hmono

/-- **`C_en⁰`, SPLIT.**

The energy-slot constant of the per-`ω` display is `Creg · 3^{(1-α)k} ·
coarseGrainingGeomFactor (4d) (s/4)`.  The middle factor is model-free
(`three_rpow_homAlpha_homK_le`); the last factor is item **D3**, and it is the
ONLY place a model-uniform input is needed. -/
theorem recutEnergySlotConst_le_of_geom {M : ABKModel d} (hd1 : 1 ≤ d)
    {Creg GEOM : ℝ} (hCreg : 0 ≤ Creg) (hlog : 4 ≤ |Real.log M.gamma|)
    (hgeom : coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
      (homS M / 4) ≤ GEOM) :
    recutEnergySlotConst Creg (homAlpha M) ((recutExponent d hd1).exponent.toReal)
        (homS M) (homK M) ≤ Creg * 729 * GEOM := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hp : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
    rw [recutExponent_toReal]; linarith only [hdR]
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hgeom0 : (0 : ℝ) ≤
      coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) :=
    coarseGrainingGeomFactor_nonneg hp (by linarith only [hs])
  have h3 := three_rpow_homAlpha_homK_le M hlog
  have hCreg729 : (0 : ℝ) ≤ Creg * 729 := by linarith only [hCreg]
  rw [recutEnergySlotConst]
  calc Creg * (3 : ℝ) ^ ((1 - homAlpha M) * (homK M : ℝ)) *
        coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4)
      ≤ Creg * 729 *
        coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCreg) hgeom0
    _ ≤ Creg * 729 * GEOM := mul_le_mul_of_nonneg_left hgeom hCreg729

/-! ## 3. THE ENERGY SUPPLY, PRODUCED FROM THE CLAUSE AND D3 -/

/-- **THE ENERGY SUPPLY OF THEOREM B'S §4.5 LANE, PRODUCED.**

`HomSeamGradProvider.SeamEnergySupplyOfRegularityGrad` from exactly two inputs:
the multiscale coarse-graining clause and one model-uniform bound `GEOM` for
the geometric factor **D3**.  Everything else is discharged:

* the three energy conjuncts come from the per-`ω` slot
  (`seamEnergySlot_of_regularityDisplayAt`) at the Theorem-C display;
* the finiteness cuts come from `ae_seam_quarter_errors_ne_top`;
* the two representative identities come from
  `Support.ae_forall_fluxCorrectedError_eq_representative`;
* the classical-gradient binder is the threaded one, i.e. the frozen root's own;
* the minimal scale is finite a.e. by the supply's own tail binder.

`C_en⁰` is `Creg · 729 · GEOM` — the `Creg` hoist of obstruction (γ), with the
D3 factor displayed once. -/
theorem seamEnergySupplyGrad_of_clause_and_geom (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar : ℝ) (hcstar : 0 < cstar) {gamma0in GEOM : ℝ} (hg0in : 0 < gamma0in)
    (hgeom : ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0in →
      coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4) ≤
        GEOM)
    (hclause : SeamMultiscaleClauseSupply d hd1 cstar gamma0in) :
    ∃ gamma0 Ctop : ℝ, 0 < gamma0 ∧ 0 ≤ Ctop ∧
      ∀ Creg : ℝ, 0 < Creg →
        SeamEnergySupplyOfRegularityGrad d hd1 cstar gamma0 (Creg * 729 * GEOM) Ctop
          Creg := by
  obtain ⟨Cstep, hCstep, hslot⟩ := seamEnergySlot_of_regularityDisplayAt d hd1
  obtain ⟨g2, hg2, hcuts⟩ := ae_seam_quarter_errors_ne_top d cstar hcstar
  refine ⟨min gamma0in g2, seamTopScaleConst d Cstep, lt_min hg0in hg2,
    seamTopScaleConst_nonneg d hCstep.le, ?_⟩
  intro Creg hCreg M hcs hgamma hlog m X hXmeas hXfin hXdisp
  have hg_in : M.gamma ≤ gamma0in := le_trans hgamma (min_le_left _ _)
  have hg_2 : M.gamma ≤ g2 := le_trans hgamma (min_le_right _ _)
  have hs : 0 < homS M := homS_pos (by linarith only [hlog])
  have hgeomM := hgeom M hcs hg_in
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
  have hconst := recutEnergySlotConst_le_of_geom hd1 hCreg.le hlog hgeomM
  exact le_trans hSb
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hF) hB)

/-! ## 4. THE DELIVERABLE -/

/-- **The frozen `generator_renormalization` body from the clause and `D₃`.**

The hypothesis list is `{0 < cstar, 0 < gamma0, 0 < Cgap, 0 ≤ GEOM}` plus the
multiscale coarse-graining clause and the ONE geometric-factor bound. Every
other input of the lane — the `C_w` envelope, the `K_abs` frame, `C_en⁰`,
`C_top`, the minimal-scale tail, the classical-gradient binder and the three
energy conjuncts — is discharged. -/
theorem generator_renormalization_provider_final_of_clause_and_geom (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0 Cgap GEOM : ℝ} (hg0 : 0 < gamma0) (hCgap : 0 < Cgap)
    (hGEOM : 0 ≤ GEOM)
    (hgeom : ∀ hd : 2 ≤ d, ∀ M : ABKModel d, Disorder.cstar M = cstar →
      M.gamma ≤ gamma0 →
      coarseGrainingGeomFactor
          ((recutExponent d (le_trans (by norm_num) hd)).exponent.toReal)
          (homS M / 4) ≤ GEOM)
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
    have hd1 : 1 ≤ d := le_trans (by norm_num) hd
    obtain ⟨g1, Ctop, hg1, hCtop, hsupply⟩ :=
      seamEnergySupplyGrad_of_clause_and_geom d hd1 cstar hcstar hg0 (hgeom hd)
        (hclause hd inst)
    have hCen0 : ∀ Creg : ℝ, 0 < Creg → (0 : ℝ) ≤ Creg * 729 * GEOM := by
      intro Creg hCreg
      have h1 : (0 : ℝ) ≤ Creg * 729 := by linarith only [hCreg]
      exact mul_nonneg h1 hGEOM
    exact generator_renormalization_provider_of_seamBundleHalfGrad d hd cstar hcstar
      (KabsF := fun Creg => recutKabsHalf d hd1 Cgap (Creg * 729 * GEOM))
      (lt_min hg1 (by norm_num)) hCgap.le
      (fun Creg hCreg => recutKabsHalf_nonneg d hd1 hCgap (hCen0 Creg hCreg)) hCtop
      (fun Creg hCreg =>
        seamBundleOfRegularityHalfGrad_of_energySupplyGrad d hd hCgap
          (hCen0 Creg hCreg) (hsupply Creg hCreg))
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma _m
    exact absurd M.shellPrefix.dimension hd

end

end Algsuperdiff.Section4.Provider.Homogenization
