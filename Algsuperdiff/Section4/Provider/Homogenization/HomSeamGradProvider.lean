/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamGradSpine
import Algsuperdiff.Section4.Provider.Homogenization.HomProviderBSeamAssemblyHalf

/-!
# The conditional provider, re-threaded: gradient binder, tail binder, `Creg` hoist

## What this file supplies

The §4.5 energy supply has four obstructions.  Three of them are ours;
this file gives them:

* **(α)** the display's classical-gradient binder is threaded all the way
  to the top, where the frozen ROOT's OWN binder re-supplies it — the
  provider introduced it as `_hgrad` and discarded it;
* **(β)** the a.e. finiteness of the minimal scale becomes an explicit binder of
  the supply and is DISCHARGED here from the Theorem-C tail
  (`ae_ne_top_of_regTail`);
* **(γ)** the Theorem-C constant `Creg` is hoisted above the `K_abs` pin, so
  `C_en⁰` — which is linear in `Creg` — may legally depend on it.

The source-facing hypothesis count is UNCHANGED: the threaded binder is the
frozen root's own, and the tail binder is discharged, not assumed.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The minimal-scale tail kills the value `⊤` -/

/-- **THE `X`-TAIL BINDER, DISCHARGED.**

`HomProviderBAssembly.exists_regularity_minimalScale` supplies, at every
admissible model, the Theorem-C tail bound

```text
  ∀ N, P[N ≤ X] ≤ C_st exp(-(1-α)²(N - C_st)/(C_st γ)).
```

Since `1 - α = s/2 > 0` and `C_st γ > 0` the right-hand side is a geometric
sequence with ratio `exp(-(1-α)²/(C_st γ)) < 1`, so it tends to `0` and the
event `{X = ⊤}`, which sits inside every `{N ≤ X}`, is null.  This is the
binder the per-`ω` energy slot needs: off it the enlarged `Y` degenerates to
`⊤` and the printed factor carries no information. -/
theorem ae_ne_top_of_regTail {d : ℕ} (M : ABKModel d) {Cst : ℝ} (hCst : 1 ≤ Cst)
    (hs : 0 < homS M) {X : Cutoff.CutoffSample d → ℕ∞}
    (htail : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
        ENNReal.ofReal (Cst *
          Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
            (Cst * M.gamma)))) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤ := by
  have hCst0 : (0 : ℝ) < Cst := lt_of_lt_of_le zero_lt_one hCst
  have hgpos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsplit : (1 : ℝ) - homAlpha M = homS M / 2 := by rw [homAlpha]; ring
  have ha : (0 : ℝ) < (1 - homAlpha M) ^ (2 : ℕ) := by
    rw [hsplit]; exact pow_pos (by linarith only [hs]) 2
  have hb : (0 : ℝ) < Cst * M.gamma := mul_pos hCst0 hgpos
  set a : ℝ := (1 - homAlpha M) ^ (2 : ℕ) with hadef
  set b : ℝ := Cst * M.gamma with hbdef
  set r : ℝ := Real.exp (-(a / b)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have hab : (0 : ℝ) < a / b := div_pos ha hb
    have hlt := Real.exp_lt_exp.mpr (show -(a / b) < (0 : ℝ) by linarith only [hab])
    rwa [Real.exp_zero] at hlt
  have hpow : ∀ N : ℕ, r ^ N = Real.exp (-(a / b) * (N : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, hrdef, ← Real.exp_add]
        congr 1
        push_cast
        ring
  have hrw : ∀ N : ℕ, Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b) =
      Cst * Real.exp (a * Cst / b) * r ^ N := by
    intro N
    have hstep : Cst * Real.exp (a * Cst / b) * r ^ N =
        Cst * (Real.exp (a * Cst / b) * Real.exp (-(a / b) * (N : ℝ))) := by
      rw [hpow N]; ring
    rw [hstep, ← Real.exp_add]
    have harg : a * Cst / b + -(a / b) * (N : ℝ) = -(a * ((N : ℝ) - Cst)) / b := by
      field_simp
      ring
    rw [harg]
  have hlim : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun N : ℕ => Cst * Real.exp (a * Cst / b) * r ^ N)
        Filter.atTop (nhds (Cst * Real.exp (a * Cst / b) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul _
    rw [mul_zero] at h0
    have hreal : Filter.Tendsto
        (fun N : ℕ => Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)) Filter.atTop
        (nhds 0) := h0.congr fun N => (hrw N).symm
    have hcomp := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa using hcomp
  rw [MeasureTheory.ae_iff]
  have hsub : ∀ N : ℕ,
      {omega : Cutoff.CutoffSample d | ¬ X omega ≠ ⊤} ⊆
        {omega : Cutoff.CutoffSample d | (N : ℕ∞) ≤ X omega} := by
    intro N omega homega
    have htop : X omega = ⊤ := not_not.mp homega
    simp only [Set.mem_setOf_eq, htop, le_top]
  have hle : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | ¬ X omega ≠ ⊤} ≤
        ENNReal.ofReal (Cst * Real.exp (-(a * ((N : ℝ) - Cst)) / b)) :=
    fun N => le_trans (measure_mono (hsub N)) (htail N)
  exact le_antisymm (ge_of_tendsto' hlim hle) (zero_le _)

/-! ## 2. The two supply layers, at a hoisted `Creg` and the tail binder -/

/-- **The energy residue of Theorem B, re-threaded.**

`HomProviderBSeamResidue.SeamEnergySupplyOfRegularity` with THREE changes:

* the classical-gradient binder of the display is threaded through
  (`RecutCoreSupplyFluxEnergyGrad`);
* the a.e. finiteness of the minimal scale is an explicit hypothesis
  (discharged from the tail by `ae_ne_top_of_regTail`);
* the Theorem-C constant `Creg` is HOISTED OUT of the `∀`-body to a parameter,
  so that the energy-slot constant `C_en⁰` — which is LINEAR in `Creg` — may
  legally depend on it.  `Creg` is model-free, so the hoist costs nothing. -/
def SeamEnergySupplyOfRegularityGrad (d : ℕ) [NeZero d] (hd1 : 1 ≤ d)
    (cstar gamma0 Cen0 Ctop Creg : ℝ) : Prop :=
  ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
    ∀ (hlog : 4 ≤ |Real.log M.gamma|) (m : ℤ),
      ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, X omega ≠ ⊤) →
        (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RegularityDisplayAt M Creg (homAlpha M) m X omega) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          RecutCoreSupplyFluxEnergyGrad M
            (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m Cen0
            hd1 hlog omega

/-- `HomProviderBSeamAssemblyHalf.SeamBundleOfRegularityHalf` with the same
three changes. -/
def SeamBundleOfRegularityHalfGrad (d : ℕ) [NeZero d]
    (cstar gamma0 Cgap Kabs Ctop Creg : ℝ) : Prop :=
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
            (Annealed.sigmaBar M m).2 Kabs omega

/-! ## 3. The reduction, re-threaded -/

/-- `HomProviderBSeamAssemblyHalf.seamBundleOfRegularityHalf_of_energySupply`,
re-threaded.  The `C_w` envelope is still DISCHARGED and `K_abs` is still the
closed term `recutKabsHalf d hd1 Cgap Cen0`. -/
theorem seamBundleOfRegularityHalfGrad_of_energySupplyGrad (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    {cstar gamma0 Cgap Cen0 Ctop Creg : ℝ} (hCgap : 0 < Cgap) (hCen0 : 0 ≤ Cen0)
    (hsupply : SeamEnergySupplyOfRegularityGrad d (le_trans (by norm_num) hd) cstar gamma0
      Cen0 Ctop Creg) :
    SeamBundleOfRegularityHalfGrad d cstar (min gamma0 (1 / 81)) Cgap
      (recutKabsHalf d (le_trans (by norm_num) hd) Cgap Cen0) Ctop Creg := by
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
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m Cen0 hd1 hlog
    (hsupply M hcs hg_s hlog m X hXmeas hXfin hXdisp)
  have hKabsC : spineClauseConst d (homS M) (recutExponent d hd1).exponent.toReal
      (recutCwHalfFluxAt d hd1 M (recutPinnedCcgFlux d (recutExponent d hd1)) Cgap Cen0)
      (stepFourSchauderConstU d) ≤ recutKabsHalf d hd1 Cgap Cen0 :=
    spineClauseConst_le_abs_half d hd1 M hCcg0 hCgap hCen0 hlog
  filter_upwards [hsupF, hfin] with omega hsupplyOmega hfinOmega
  exact spineDatumCoarseGrainingRecutFluxAtHalfGrad_of_core_pinned hd M Cgap
    (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
    (homSeamBase M hs) (Annealed.sigmaBar M m).2 hCcg0 hCcgDom omega
    (spineDatumRecutCoreFluxAtHalfGrad_of_supply hd1 M
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m hs hCcg0
      omega hlog hgamma1 hCgap hCen0 hfinOmega hKabsC hsupplyOmega)

/-! ## 4. The spine endpoint at the re-threaded bundle -/

/-- `HomProviderBSeamAssemblyHalf.homogenization_spine_close_of_seamBundleHalf`,
re-threaded. -/
theorem homogenization_spine_close_of_seamBundleHalfGrad (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
              SpineDatumCoarseGrainingRecutFluxHalfGrad M Cgap
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
    homogenization_spine_close_of_stepOneDisplayGrad d cstar hcstar (Cgap := Cgap)
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
    homSpineClauseSupplierAtGrad_of_datumRecutFluxHalfGrad hd M Cgap
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
      (homSeamBase M hs) (Annealed.sigmaBar M m).2 omega hb

/-! ## 5. THE CONDITIONAL PROVIDER, re-threaded -/

/-- **The frozen `generator_renormalization` body from the re-threaded seam
bundle.**

The root's own `HasGradientOn` binder is now CONSUMED, not discarded; the
minimal-scale tail binder is discharged from the tail; and the `K_abs` slot is
a FUNCTION of the Theorem-C constant `Creg`, pinned only after
`exists_regularity_minimalScale` has produced it. -/
theorem generator_renormalization_provider_of_seamBundleHalfGrad (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) {gamma0res Cgap Ctop : ℝ}
    {KabsF : ℝ → ℝ} (hg0res : 0 < gamma0res) (hCgap : 0 ≤ Cgap)
    (hKabs : ∀ Creg : ℝ, 0 < Creg → 0 ≤ KabsF Creg) (hCtop : 0 ≤ Ctop)
    (hcore : ∀ Creg : ℝ, 0 < Creg →
      SeamBundleOfRegularityHalfGrad d cstar gamma0res Cgap (KabsF Creg) Ctop Creg) :
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
    homogenization_spine_close_of_seamBundleHalfGrad d hd cstar hcstar (Cst := Cst)
      (Cgap := Cgap) (Kabs := KabsF Creg) (Ctop := Ctop) hCst hCgap (hKabs Creg hCreg) hCtop
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
