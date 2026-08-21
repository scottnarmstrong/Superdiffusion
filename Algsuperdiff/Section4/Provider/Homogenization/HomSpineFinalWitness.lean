/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomStepOneDisplay

/-!
# Theorem B, §4.5: the REAL defect witness `E_B` and its moment (clause C2)

## What this is

The frozen root asks for a **real-valued** `E_B: Ω → ℝ` with

```text
  0 ≤ E_B,   E_B measurable,
  ∫⁻ (ofReal E_B)^p ≤ ( C (√p + √|log γ|) √γ (log γ)² )^p
      for every p ∈ [1, C⁻¹ γ⁻¹ |log γ|⁻¹].
```

This repository's carrier `EthmB(m)` is `[0,∞]`-valued
(`HomStepEnvelope.ethmB`), so the real cut needs `EthmB < ∞` a.e.  That is
certified here, and the cut is made:

```text
  E_B(ω):= K · (EthmB(m)(ω)).toReal.
```

`K` is the Step-3/Step-4 absorption factor (the constant the manuscript
"absorbs into `EthmB(m)`" in the paper), carried as a parameter and paid for in
the constant `C`, exactly as `ethmB_const_smul_moment` prices it.

## The chain, and where each link comes from

```text
  hY  (the Theorem-C minimal-scale exponential moment, the single edge)
    → HomStepOneDisplay.exists_ethmB_moment_bound     (Step 1's display)
    → HomStepEnvelope.ethmB_const_smul_moment          (the rescaling)
    → ofReal (E_B ω) ≤ ofReal K · EthmB(m)(ω)          (the real cut, everywhere)
    → ∀ᵐ ω, EthmB(m)(ω) ≠ ∞                            (from the p = 1 moment)
    → the LINKAGE:  ofReal D ≤ EthmB(m)(ω)  ⟹  K·D ≤ E_B(ω).
```

The last item is the interface every downstream clause producer needs: it turns
an `[0,∞]`-valued domination of a real defect quantity by `EthmB(m)` — which is
what `HomStepThreeCoarse.ethmB_ge_first_summand` and
`HomStepEnvelope.ethmB_ge_gap` deliver — into the real inequality
`K·D ≤ E_B(ω)` that clauses (C3) and (C4) consume.  Nothing else about `E_B` is
exposed, so no downstream step can see the `[0,∞]` carrier, and no step can use
`E_B` on the null set where the carrier is infinite.

## The conditional set (exactly one edge, and it is the)

`hY` — the exponential moment `𝔼[(3^{(1-α)X_m(α)})^{2p}] ≤ 2^{2p}` of the
Theorem-C minimal-scale factor, at the single exponent Step 1 consumes, stated
here for an ABSTRACT `[0,∞]`-valued `Y` on the range
`p ≤ C_gate⁻¹ γ⁻¹ |log γ|⁻¹`.  Theorem C is a declared dependency of the
Step 1 (the moment bound), and the
`HomSpineGamma0.homY_moment_bound_of_gamma_le` produces exactly this hypothesis
from the transcribed `hC` tail at `C_gate = homGateRangeConst C⋆` and
`γ ≤ homGamma0 C⋆`.

**BLOCKED COMPOSITION (a tree defect, reported and still open).**  That
composition cannot be written in any module today: `HomStepOneAnchor` and
`HomSpineGamma0` BOTH declare `homGamma0` and `homGamma0_pos` in this namespace
(`HomStepOneAnchor.lean` versus `HomSpineGamma0.lean`), so no Lean module may
import both cones.  Resolving it is a rename of one of the two pairs; until that
is done, `hY` stays a binder here, at the exact shape
`homY_moment_bound_of_gamma_le` delivers.

## The constants

```text
  C:= K·C₀(1 + C_gap) + C₀ + C_gate + 1,
  γ₀:= min( γ₀^{Step 1}, 1/81, (4C)⁻² ),
```

with `C₀` the Step-1 constant.  The summands beyond the first make the root's
own `p`-range `p ≤ C⁻¹γ⁻¹|log γ|⁻¹` imply BOTH sub-ranges (the and `hY`'s);
the `1/81` clause buys `|log γ| ≥ 4` and the `(4C)⁻²` clause buys `p = 1` inside
the range, which is where the a.e. finiteness of `EthmB(m)` comes from.
-/

open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Two elementary transfers -/

/-- Shrinking a reciprocal range: a `p`-range stated at the larger constant is
contained in the `p`-range stated at the smaller one. -/
theorem range_mono_of_le {K C gam Lg p : ℝ} (hK : 0 < K) (hKC : K ≤ C)
    (hgam : 0 ≤ gam⁻¹) (hLg : 0 ≤ Lg⁻¹) (hp : p ≤ C⁻¹ * gam⁻¹ * Lg⁻¹) :
    p ≤ K⁻¹ * gam⁻¹ * Lg⁻¹ := by
  have hCpos : 0 < C := lt_of_lt_of_le hK hKC
  have hinv : C⁻¹ ≤ K⁻¹ := by
    rw [inv_le_inv₀ hCpos hK]
    exact hKC
  have hstep : C⁻¹ * gam⁻¹ * Lg⁻¹ ≤ K⁻¹ * gam⁻¹ * Lg⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv hgam) hLg
  linarith only [hp, hstep]

/-- `γ|log γ| ≤ 4√γ` on `0 < γ < 1`: the `absLog_mul_sqrt_le` multiplied by
`√γ` and collapsed with `t³ ≤ t²` at `t = γ^{1/4} ≤ 1`.  This is the only place
a logarithm meets a power of `γ` in this module; it is spent exactly once, to
put `p = 1` inside the theorem's own range. -/
theorem gamma_mul_absLog_le {gamma : ℝ} (hg : 0 < gamma) (hg1 : gamma < 1) :
    gamma * |Real.log gamma| ≤ 4 * Real.sqrt gamma := by
  have htpos : 0 < Real.sqrt (Real.sqrt gamma) := quarticRoot_pos hg
  have htsq : Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) = Real.sqrt gamma :=
    quarticRoot_sq gamma
  have ht1 : Real.sqrt (Real.sqrt gamma) ≤ 1 :=
    sqrt_le_one_of_le_one (sqrt_le_one_of_le_one hg1.le)
  have hkey := absLog_mul_sqrt_le hg hg1
  have hsqnn : (0 : ℝ) ≤ Real.sqrt gamma := Real.sqrt_nonneg gamma
  have hgeq : gamma * |Real.log gamma| =
      Real.sqrt gamma * (|Real.log gamma| * Real.sqrt gamma) := by
    rw [mul_comm |Real.log gamma| (Real.sqrt gamma), ← mul_assoc,
      Real.mul_self_sqrt hg.le]
  have hcube : Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * Real.sqrt (Real.sqrt gamma) ≤
      Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * 1 :=
    mul_le_mul_of_nonneg_left ht1 (by positivity)
  calc gamma * |Real.log gamma|
      = Real.sqrt gamma * (|Real.log gamma| * Real.sqrt gamma) := hgeq
    _ ≤ Real.sqrt gamma * (4 * Real.sqrt (Real.sqrt gamma)) :=
        mul_le_mul_of_nonneg_left hkey hsqnn
    _ = 4 * (Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * Real.sqrt (Real.sqrt gamma)) := by
        rw [htsq]; ring
    _ ≤ 4 * (Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) * 1) := by
        linarith only [hcube]
    _ = 4 * Real.sqrt gamma := by rw [htsq]; ring

/-! ## 2. The witness -/

/-- **The real defect witness of clause (C2), with its moment and its linkage.**

`E_B(ω) = K · (EthmB(m)(ω)).toReal`, conditional on `hY` alone; the constants
`γ₀` and `C` are explicit in `C_gate`, `C_gap`, `K` and the `C₀`.

The fourth conclusion is the LINKAGE: on a set of full measure, every real `D`
dominated by `EthmB(m)(ω)` in `[0,∞]` obeys `K·D ≤ E_B(ω)`.  This is what makes
the real cut usable downstream; it is where the a.e. finiteness of `EthmB(m)`
is spent, and it is spent nowhere else. -/
theorem exists_spine_defect_witness (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar)
    {Cgate Cgap Kabs : ℝ} (hCgate : 0 < Cgate) (hCgap : 0 ≤ Cgap)
    (hKabs : 0 ≤ Kabs) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
          (∀ p : ℝ, 1 ≤ p → p ≤ Cgate⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ omega, Y omega ^ (2 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal 2 ^ (2 * p)) →
          ∀ hs : 0 < homS M, ∀ m : ℤ,
            ∃ EB : Cutoff.CutoffSample d → ℝ,
              (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
              (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
                (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                  ENNReal.ofReal
                      (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                        Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p) ∧
              (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                ∀ D : ℝ, 0 ≤ D →
                  ENNReal.ofReal D ≤
                      ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega →
                    Kabs * D ≤ EB omega) := by
  obtain ⟨g1, C0, hg1pos, hC0, hHG1⟩ := exists_ethmB_moment_bound d cstar hcstar
  have hC0pos : (0 : ℝ) < C0 := lt_of_lt_of_le zero_lt_one hC0
  set C : ℝ := Kabs * C0 * (1 + Cgap) + C0 + Cgate + 1 with hCdef
  have hKC0 : (0 : ℝ) ≤ Kabs * C0 * (1 + Cgap) := by
    have h1 : (0 : ℝ) ≤ Kabs * C0 := mul_nonneg hKabs hC0pos.le
    have h2 : (0 : ℝ) ≤ 1 + Cgap := by linarith only [hCgap]
    exact mul_nonneg h1 h2
  have hCpos : 0 < C := by
    rw [hCdef]; linarith only [hKC0, hC0pos, hCgate]
  have hCquart : (0 : ℝ) < ((4 * C)⁻¹) ^ (2 : ℕ) := by
    have h4 : (0 : ℝ) < 4 * C := by linarith only [hCpos]
    exact pow_pos (inv_pos.mpr h4) 2
  refine ⟨min g1 (min (1 / 81) (((4 * C)⁻¹) ^ (2 : ℕ))), C,
    lt_min hg1pos (lt_min (by norm_num) hCquart), hCpos, ?_⟩
  intro M hcs hgamma Y hYmeas hY hs m
  /- ### the `γ`-consequences of the thresho -/
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_g1 : M.gamma ≤ g1 := le_trans hgamma (min_le_left _ _)
  have hg_81 : M.gamma ≤ 1 / 81 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg_C : M.gamma ≤ ((4 * C)⁻¹) ^ (2 : ℕ) :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_right _ _))
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg_81
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hg1lt : M.gamma < 1 := by linarith only [hg_81]
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgpos).le
  have hLinv : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ := (inv_pos.mpr hLpos).le
  /- ### `p = 1` lies inside the theorem's own ran -/
  have hsqrtC : Real.sqrt M.gamma ≤ (4 * C)⁻¹ := by
    have h4 : (0 : ℝ) < 4 * C := by linarith only [hCpos]
    have hpow : Real.sqrt M.gamma ^ (2 : ℕ) ≤ ((4 * C)⁻¹) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hgpos.le]; exact hg_C
    exact le_of_pow_le_pow_left₀ (by norm_num) (inv_pos.mpr h4).le hpow
  have hprod : C * (M.gamma * |Real.log M.gamma|) ≤ 1 := by
    have h4 : (0 : ℝ) < 4 * C := by linarith only [hCpos]
    have hstep := gamma_mul_absLog_le hgpos hg1lt
    have hmul : C * (M.gamma * |Real.log M.gamma|) ≤ C * (4 * Real.sqrt M.gamma) :=
      mul_le_mul_of_nonneg_left hstep hCpos.le
    have hfin : (4 * C) * Real.sqrt M.gamma ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hsqrtC h4.le
      rwa [mul_inv_cancel₀ (ne_of_gt h4)] at h
    linarith only [hmul, hfin]
  have hone : (1 : ℝ) ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
    have hppos : (0 : ℝ) < C * M.gamma * |Real.log M.gamma| :=
      mul_pos (mul_pos hCpos hgpos) hLpos
    have hid : (C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹) *
        (C * M.gamma * |Real.log M.gamma|) = 1 := by
      field_simp
    have hle : 1 * (C * M.gamma * |Real.log M.gamma|) ≤
        (C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹) *
          (C * M.gamma * |Real.log M.gamma|) := by
      rw [hid, one_mul, mul_assoc]
      exact hprod
    exact le_of_mul_le_mul_right hle hppos
  /- ### Step 1's display at the carri -/
  have hSeq : homS M = |Real.log M.gamma|⁻¹ := rfl
  have hmom : ∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal
            (C0 * (1 + Cgap) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p := by
    intro p hp hrange
    have hsub : p ≤ C0⁻¹ * M.gamma⁻¹ * homS M := by
      rw [hSeq]
      exact range_mono_of_le hC0pos (by rw [hCdef]; linarith only [hKC0, hCgate]) hginv
        hLinv hrange
    have hgate : p ≤ Cgate⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ :=
      range_mono_of_le hCgate (by rw [hCdef]; linarith only [hKC0, hC0pos]) hginv hLinv
        hrange
    exact hHG1 M hcs hg_g1 hs m Y hYmeas.aemeasurable Cgap hCgap p hp hsub
      (hY p hp hgate)
  /- ### a.e. finiteness of the carrier, from the `p = 1` instan -/
  have hmeas : Measurable (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩) :=
    measurable_ethmB M Cgap hYmeas (homN_le M m) _
  have hfin : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ≠ ⊤ := by
    have h1 := hmom 1 le_rfl hone
    have hrw : (∫⁻ omega, ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫⁻ omega, ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega ^ (1 : ℝ)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      refine lintegral_congr fun omega => ?_
      rw [ENNReal.rpow_one]
    have hne : (∫⁻ omega, ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≠ ⊤ := by
      rw [hrw]
      refine ne_top_of_le_ne_top ?_ h1
      rw [ENNReal.rpow_one]
      exact ENNReal.ofReal_ne_top
    exact (ae_lt_top' hmeas.aemeasurable hne).mono fun omega homega => homega.ne
  /- ### the real c -/
  refine ⟨fun omega => Kabs * (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal,
    fun omega => mul_nonneg hKabs ENNReal.toReal_nonneg,
    hmeas.ennreal_toReal.const_mul Kabs, ?_, ?_⟩
  · /- the moment display, after the cut and the rescali -/
    intro p hp hrange
    have hp0 : (0 : ℝ) ≤ p := by linarith only [hp]
    have hpt : ∀ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal
            (Kabs * (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal) ≤
          ENNReal.ofReal Kabs * ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega := by
      intro omega
      rw [ENNReal.ofReal_mul hKabs]
      exact mul_le_mul' (le_refl _) ENNReal.ofReal_toReal_le
    have hmono : (∫⁻ omega,
        ENNReal.ofReal
            (Kabs * (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal) ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ∫⁻ omega,
          (ENNReal.ofReal Kabs * ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega) ^ p
            ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
      lintegral_mono fun omega => ENNReal.rpow_le_rpow (hpt omega) hp0
    have hscale := ethmB_const_smul_moment M Cgap (Y := Y) (m := m) (n := homN M m)
      (s := ⟨homS M, hs⟩) hp0 hKabs (hmom p hp hrange)
    refine (hmono.trans hscale).trans ?_
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0
    have hT : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by positivity
    have hfac : Kabs * C0 * (1 + Cgap) ≤ C := by
      rw [hCdef]; linarith only [hC0pos, hCgate]
    have hstep := mul_le_mul_of_nonneg_right hfac hT
    calc Kabs * (C0 * (1 + Cgap) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ))
        = Kabs * C0 * (1 + Cgap) *
            ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
              Real.log M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ C * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            Real.log M.gamma ^ (2 : ℕ)) := hstep
      _ = C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            Real.log M.gamma ^ (2 : ℕ) := by ring
  · /- the linka -/
    refine hfin.mono fun omega hne D hD hle => ?_
    have hreal : D ≤ (ethmB M Cgap Y m (homN M m) ⟨homS M, hs⟩ omega).toReal := by
      have h := ENNReal.toReal_mono hne hle
      rwa [ENNReal.toReal_ofReal hD] at h
    exact mul_le_mul_of_nonneg_left hreal hKabs

end

end Algsuperdiff.Section4.Provider.Homogenization
