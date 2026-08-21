/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxBundle

/-!
# Theorem B, §4.5: the spine at a FREE `EthmB` base and a FREE `Y`

## Why this file exists

The authorized re-pin moves the `EthmB(m)` base exponent from the printed
`s = |log γ|⁻¹` to `s/8`, and the index change enlarges the printed `Y` slot
by two more error factors (`HomSpineTopScale.stepTwoEnlargedY`).  Both moves are
INSIDE the own carrier `ethmB M Cgap Y m n sb`, and every
spine module (`HomSpineFinalWitness`, `HomSpineFinalEndpoint`,
`HomSpineCloseGate`, `HomSpineCloseFinal`) hard-codes

```text
  Y  = homMinimalScaleFactor (1 - α) X,      sb = ⟨homS M, hs⟩.
```

This file re-states that chain with `Y` and `sb` FREE, and with the single thing
those modules used them for — Step 1's moment display — taken as an explicit
hypothesis `StepOneDisplayAt`.  Nothing else changes: the real cut `E_B`, the
linkage, clauses (C1)/(C2), and the passage to the root's conclusion body are
the arguments verbatim.

## The three statements

```text
  exists_spine_defect_witness_of_display     — (C2) and the linkage, at (Y, sb);
  homogenization_spine_endpoint_of_display   — the root's body from the display,
                                               (C1) and the clause supplier;
  homogenization_spine_close_of_stepOneDisplay
                                             — the same with (C1) discharged off
                                               the Section-3 anchor.
```

`hY` does NOT appear: at a free `Y` the Theorem-C exponential moment is not a
statement about `Y` at all, and the composite it fed (`Y`'s own `2p`-moment)
lives inside `StepOneDisplayAt`, where the consumer discharges it.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Step 1's display, as a named input at a free base -/

/-- **STEP 1's DISPLAY the `𝓔` estimate at a free `Y` and a free base.**

`HomStepOneDisplay.exists_ethmB_moment_bound` is exactly this `Prop` at `Y =
homMinimalScaleFactor (1-α) X` and `sb = ⟨homS M, hs⟩`; the `s/8` sibling at
the enlarged `Y` is this file.  The `p`-range is the display's own, at the
display's own constant. -/
def StepOneDisplayAt (M : ABKModel d) (Cgap : ℝ) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m : ℤ) (sb : {s : ℝ // 0 < s}) (C0 : ℝ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → p ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
    (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal
          (C0 * (1 + Cgap) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p

/-! ## 2. The real defect witness -/

/-- **The real defect witness of clause (C2), at a free `(Y, sb)`.**

`HomSpineFinalWitness.exists_spine_defect_witness` with Step 1's display taken
as the hypothesis instead of being re-derived from `hY`: `E_B(ω) =
K·(EthmB(m)(ω)).toReal`, its moment at the root's own constant shape, and the
LINKAGE that turns an `[0,∞]`-domination of a real defect into `K·D ≤ E_B(ω)`.

The a.e. finiteness of the carrier is again spent exactly once, at `p = 1`. -/
theorem exists_spine_defect_witness_of_display (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar)
    {Cgap Kabs C0 : ℝ} (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs) (hC0 : 1 ≤ C0) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
          ∀ (m : ℤ) (sb : {s : ℝ // 0 < s}),
            StepOneDisplayAt M Cgap Y m sb C0 →
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
                  ENNReal.ofReal D ≤ ethmB M Cgap Y m (homN M m) sb omega →
                    Kabs * D ≤ EB omega) := by
  have hC0pos : (0 : ℝ) < C0 := lt_of_lt_of_le zero_lt_one hC0
  set C : ℝ := Kabs * C0 * (1 + Cgap) + C0 + 1 with hCdef
  have hKC0 : (0 : ℝ) ≤ Kabs * C0 * (1 + Cgap) := by
    have h1 : (0 : ℝ) ≤ Kabs * C0 := mul_nonneg hKabs hC0pos.le
    have h2 : (0 : ℝ) ≤ 1 + Cgap := by linarith only [hCgap]
    exact mul_nonneg h1 h2
  have hCpos : 0 < C := by
    rw [hCdef]; linarith only [hKC0, hC0pos]
  have hCquart : (0 : ℝ) < ((4 * C)⁻¹) ^ (2 : ℕ) := by
    have h4 : (0 : ℝ) < 4 * C := by linarith only [hCpos]
    exact pow_pos (inv_pos.mpr h4) 2
  refine ⟨min (1 / 81) (((4 * C)⁻¹) ^ (2 : ℕ)), C,
    lt_min (by norm_num) hCquart, hCpos, ?_⟩
  intro M _hcs hgamma Y hYmeas m sb hdisp
  /- ### the `γ`-consequences of the thresho -/
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_81 : M.gamma ≤ 1 / 81 := le_trans hgamma (min_le_left _ _)
  have hg_C : M.gamma ≤ ((4 * C)⁻¹) ^ (2 : ℕ) := le_trans hgamma (min_le_right _ _)
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
  /- ### the display, on the theorem's own ran -/
  have hmom : ∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal
            (C0 * (1 + Cgap) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) ^ p := by
    intro p hp hrange
    exact hdisp p hp
      (range_mono_of_le hC0pos (by rw [hCdef]; linarith only [hKC0]) hginv hLinv hrange)
  /- ### a.e. finiteness of the carrier, from the `p = 1` instan -/
  have hmeas : Measurable (ethmB M Cgap Y m (homN M m) sb) :=
    measurable_ethmB M Cgap hYmeas (homN_le M m) _
  have hfin : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ethmB M Cgap Y m (homN M m) sb omega ≠ ⊤ := by
    have h1 := hmom 1 le_rfl hone
    have hrw : (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega ^ (1 : ℝ)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      refine lintegral_congr fun omega => ?_
      rw [ENNReal.rpow_one]
    have hne : (∫⁻ omega, ethmB M Cgap Y m (homN M m) sb omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≠ ⊤ := by
      rw [hrw]
      refine ne_top_of_le_ne_top ?_ h1
      rw [ENNReal.rpow_one]
      exact ENNReal.ofReal_ne_top
    exact (ae_lt_top' hmeas.aemeasurable hne).mono fun omega homega => homega.ne
  /- ### the real c -/
  refine ⟨fun omega => Kabs * (ethmB M Cgap Y m (homN M m) sb omega).toReal,
    fun omega => mul_nonneg hKabs ENNReal.toReal_nonneg,
    hmeas.ennreal_toReal.const_mul Kabs, ?_, ?_⟩
  · /- the moment display, after the cut and the rescali -/
    intro p hp hrange
    have hp0 : (0 : ℝ) ≤ p := by linarith only [hp]
    have hpt : ∀ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (Kabs * (ethmB M Cgap Y m (homN M m) sb omega).toReal) ≤
          ENNReal.ofReal Kabs * ethmB M Cgap Y m (homN M m) sb omega := by
      intro omega
      rw [ENNReal.ofReal_mul hKabs]
      exact mul_le_mul' (le_refl _) ENNReal.ofReal_toReal_le
    have hmono : (∫⁻ omega,
        ENNReal.ofReal (Kabs * (ethmB M Cgap Y m (homN M m) sb omega).toReal) ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ∫⁻ omega, (ENNReal.ofReal Kabs * ethmB M Cgap Y m (homN M m) sb omega) ^ p
            ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
      lintegral_mono fun omega => ENNReal.rpow_le_rpow (hpt omega) hp0
    have hscale := ethmB_const_smul_moment M Cgap (Y := Y) (m := m) (n := homN M m)
      (s := sb) hp0 hKabs (hmom p hp hrange)
    refine (hmono.trans hscale).trans ?_
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0
    have hT : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by positivity
    have hfac : Kabs * C0 * (1 + Cgap) ≤ C := by
      rw [hCdef]; linarith only [hC0pos]
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
    have hreal : D ≤ (ethmB M Cgap Y m (homN M m) sb omega).toReal := by
      have h := ENNReal.toReal_mono hne hle
      rwa [ENNReal.toReal_ofReal hD] at h
    exact mul_le_mul_of_nonneg_left hreal hKabs

/-! ## 3. The spine endpoint at a free `(Y, sb)` -/

/-- **THE SPINE ENDPOINT AT A FREE `(Y, sb)` — the frozen root's conclusion body.**

`HomSpineFinalEndpoint.homogenization_spine_endpoint` with the `EthmB(m)` base
and the `Y` slot free, the witness taken from
`exists_spine_defect_witness_of_display`, and the clause supplier read at
`HomSeamFluxBundle.HomSpineClauseSupplierAt`.  Every clause of the root is
produced in the root's own quantifier order and at the root's own carriers. -/
theorem homogenization_spine_endpoint_of_display (d : ℕ) [NeZero d] (cstar : ℝ)
    (hcstar : 0 < cstar) {Cgap Kabs C0 Cflow : ℝ} (hCgap : 0 ≤ Cgap)
    (hKabs : 0 ≤ Kabs) (hC0 : 1 ≤ C0) (hCflow : 0 ≤ Cflow) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
          ∀ (m : ℤ) (sb : {s : ℝ // 0 < s}),
            StepOneDisplayAt M Cgap Y m sb C0 →
            ∀ sigmaBarM : ℝ, 0 < sigmaBarM →
            |sigmaBarM -
                Real.sqrt (M.nu ^ (2 : ℕ) +
                  cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
              Cflow * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM →
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              HomSpineClauseSupplierAt M Cgap Y m sb sigmaBarM Kabs omega) →
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
  obtain ⟨g0, Cwit, hg0, hCwit, hwit⟩ :=
    exists_spine_defect_witness_of_display d cstar hcstar hCgap hKabs hC0
  refine ⟨g0, Cwit + Cflow, hg0, by linarith only [hCwit, hCflow], ?_⟩
  intro M hcs hgamma Y hYm m sb hdisp sigmaBarM hsig hC1 hclauses
  obtain ⟨EB, hEB0, hEBm, hEBmom, hlink⟩ := hwit M hcs hgamma Y hYm m sb hdisp
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgpos).le
  have hLinv : (0 : ℝ) ≤ |Real.log M.gamma|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  refine ⟨sigmaBarM, hsig, ?_, EB, hEB0, hEBm, ?_, ?_⟩
  · /- (C1), re-based at the endpoint's own consta -/
    have hT : (0 : ℝ) ≤ Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hsig.le
    refine hC1.trans ?_
    calc Cflow * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM
        = Cflow * (Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM) := by ring
      _ ≤ (Cwit + Cflow) * (Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCwit]) hT
      _ = (Cwit + Cflow) * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM := by ring
  · /- (C2), re-based at the endpoint's own consta -/
    intro p hp hrange
    have hp0 : (0 : ℝ) ≤ p := by linarith only [hp]
    have hsub : p ≤ Cwit⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ :=
      range_mono_of_le hCwit (by linarith only [hCflow]) hginv hLinv hrange
    refine (hEBmom p hp hsub).trans ?_
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0
    have hT : (0 : ℝ) ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by positivity
    calc Cwit * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          Real.log M.gamma ^ (2 : ℕ)
        = Cwit * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
            Real.log M.gamma ^ (2 : ℕ)) := by ring
      _ ≤ (Cwit + Cflow) * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCflow]) hT
      _ = (Cwit + Cflow) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * Real.log M.gamma ^ (2 : ℕ) := by ring
  · /- (C3) and (C4), through the linka -/
    refine (hlink.and hclauses).mono ?_
    rintro omega ⟨hlk, hsupply⟩ L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
    obtain ⟨D, hD0, hDdom, hC3, hC4⟩ :=
      hsupply L hL u v h g Kg Kh KhInf hsol hcomp hKg hKh hKhInf
    have hKD : Kabs * D ≤ EB omega := hlk D hD0 hDdom
    have hbr : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
      dataBracket_nonneg_of_binders (h := h) (g := g) hsig hKg hKh hKhInf
    refine ⟨hC3.mono fun x hx => hx.trans ?_, hC4.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hKD hbr
    · exact mul_le_mul_of_nonneg_right hKD (sq_nonneg _)

/-! ## 4. The spine, with (C1) discharged -/

/-- **THE SPINE AT A FREE `(Y, sb)`, at `{StepOneDisplayAt, hclauses}`.**

`HomSpineCloseFinal.homogenization_spine_close` with the base and the `Y` slot
free: clause (C1) is discharged off the Section-3 anchor
`Algsuperdiff.Frozen.Section3.induction_bounds` at the genuine running
diffusivity `Annealed.sigmaBar M m`, exactly as there.

`htail` does not appear here: at a free `Y` the Theorem-C tail is consumed by
the producer of `StepOneDisplayAt`, not by the spine. -/
theorem homogenization_spine_close_of_stepOneDisplay (d : ℕ) [NeZero d] (cstar : ℝ)
    (hcstar : 0 < cstar) {Cgap Kabs C0 : ℝ} (hCgap : 0 ≤ Cgap) (hKabs : 0 ≤ Kabs)
    (hC0 : 1 ≤ C0) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ Y : Cutoff.CutoffSample d → ℝ≥0∞, Measurable Y →
          ∀ (m : ℤ) (sb : {s : ℝ // 0 < s}),
            StepOneDisplayAt M Cgap Y m sb C0 →
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              HomSpineClauseSupplierAt M Cgap Y m sb
                ((Annealed.sigmaBar M m : ℝ)) Kabs omega) →
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
  obtain ⟨Cib, hCib, hbounds⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  have hcinv : (0 : ℝ) ≤ cstar⁻¹ ^ (2 : ℕ) := pow_nonneg (inv_nonneg.mpr hcstar.le) 2
  have hCflow : (0 : ℝ) ≤ Cib * cstar⁻¹ ^ (2 : ℕ) := mul_nonneg hCib.le hcinv
  obtain ⟨g0, C, hg0, hC, hend⟩ :=
    homogenization_spine_endpoint_of_display d cstar hcstar (Cgap := Cgap)
      (Kabs := Kabs) (C0 := C0) (Cflow := Cib * cstar⁻¹ ^ (2 : ℕ)) hCgap hKabs hC0 hCflow
  have hreg0 : (0 : ℝ) < (Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ) :=
    mul_pos (pow_pos (inv_pos.mpr hCib) 10) (pow_pos hcstar 10)
  refine ⟨min g0 ((Cib⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ)), C, lt_min hg0 hreg0, hC, ?_⟩
  intro M hcs hgamma Y hY m sb hdisp hclauses
  have hreg : M.gamma ≤ (Cib⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
    rw [hcs]
    exact le_trans hgamma (min_le_right _ _)
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hC1 := (hbounds M hreg).2 m
  rw [hcs] at hC1
  exact hend M hcs (le_trans hgamma (min_le_left _ _)) Y hY m sb hdisp
    ((Annealed.sigmaBar M m : ℝ)) hsig hC1 hclauses

end

end Algsuperdiff.Section4.Provider.Homogenization
