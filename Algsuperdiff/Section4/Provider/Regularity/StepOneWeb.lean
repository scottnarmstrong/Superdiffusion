/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.MinimalScaleX
import Algsuperdiff.Section4.Provider.Regularity.StepOneEpsilon

/-!
# concrete parameters

## What is delivered

`stepOne_parameterWeb` is ABK26 `t.regularity` Step 1 as one theorem: for every
dimension `d`, every `c⋆ > 0` and every pair of abstract `d`-constants `C_edos`
(the excess-decay one-step constant, floored at 1) and `C_iter` (the Step-6
iteration constant), it produces

* the Step-1 constant `C₁`, satisfying the largeness demands — three of them
  visible in the statement (`C₁ ≥ 2`, `C₁ ≥ 2d+2`, `C₁ ≥ 4C_iter(k+1)/log 3`),
  the fourth (the `δ₀` threshold) consumed inside, where it produces the
  `ε_j(z)` display;
* the regime threshold `γ₀ = γ₀(d, c⋆)` and the `α`-range constant
  `C = C(d, c⋆)`;

and then, for every model in that regime and every `α` in that range, ALL of

1. `δ = C₁⁻¹(1-α) ∈ (0, 1/2]` — the tolerance window of
   `p.minimal.scale.separation.sec4` (: the consumer level is `δ ≤ 1/4`, inside
   the producer's range);
2. the annular-admissibility bullet at the strengthened hypothesis;
3. the `ε_j(z)` cap at the Step-1 display value `½ s^{3/2} C_edos⁻¹ 3^{-k/4}`,
   for every scale and centre;

`step_two_minimalScaleX_stepOne` is that re-export alone.

## The `k`-pin, discharged

Here `k` is the printed `⌈4 log₃(2 s^{-3/2} C_edos)⌉` and the pin is from the
explicit floor `1 ≤ C_edos` (`stepOneK_ge_ten`).  Nothing in the web assumes a
value of `C_edos` beyond that floor.

## Recorded: what is NOT discharged here

* The Step-6 demand `C₁ ≥ 4C(k+1)/log 3` is delivered as an inequality against
  the abstract `C_iter`; its consumer (Step 6) must instantiate `C_iter` with
  the iteration lemma's own constant.

## References

* ABK26, `t.regularity` Steps 1--2.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

/-- **`t.regularity` Step 1: the parameter web.**

See the module docstring for the four delivered items. -/
theorem stepOne_parameterWeb (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar)
    (Cedos Citer : ℝ) (hCedos : 1 ≤ Cedos) :
    ∃ C1 gamma0 C : ℝ,
      2 ≤ C1 ∧ 2 * (d : ℝ) + 2 ≤ C1 ∧
      4 * Citer * ((stepOneK Cedos : ℝ) + 1) / Real.log 3 ≤ C1 ∧
      0 < gamma0 ∧ gamma0 ≤ 1 / 256 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              stepOneEp (stepOneDelta C1 alpha) ∧
          (∀ (j : ℤ) (z : Vec d),
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              stepOneEpsJ M j z (stepOneDelta C1 alpha) omega ≤
                ENNReal.ofReal
                  (1 / 2 * Real.rpow stepOneS (3 / 2 : ℝ) * Cedos⁻¹ *
                    Real.rpow (3 : ℝ) (-(stepOneK Cedos : ℝ) / 4))) ∧
          ∀ m : ℤ, ∃ Z : Cutoff.CutoffSample d → ℕ∞,
            Measurable Z ∧
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m → Z omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha)
                  stepOneSEighth_pos n m omega) ∧
            Measurable (minimalScaleX Z (stepOneK Cedos)) ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure
                    {omega | (N : ℕ∞) ≤ minimalScaleX Z (stepOneK Cedos) omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m →
                minimalScaleX Z (stepOneK Cedos) omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha)
                  stepOneSEighth_pos n m omega := by
  obtain ⟨Cann, hCannpos, hcap⟩ := ae_stepOneEpsJ_le d
  have hCedos0 : (0 : ℝ) < Cedos := lt_of_lt_of_le one_pos hCedos
  have hk : 10 ≤ stepOneK Cedos := stepOneK_ge_ten hCedos
  have hC1two : (2 : ℝ) ≤ stepOneC1 d Cedos Cann Citer (stepOneK Cedos) :=
    two_le_stepOneC1 d Cedos Cann Citer (stepOneK Cedos)
  have hC1pos : (0 : ℝ) < stepOneC1 d Cedos Cann Citer (stepOneK Cedos) :=
    stepOneC1_pos d Cedos Cann Citer (stepOneK Cedos)
  obtain ⟨g0, C0, hg0pos, hC0pos, hRG1⟩ :=
    step_two_minimalScaleX d cstar hcstar (stepOneK Cedos) hk
      (stepOneC1 d Cedos Cann Citer (stepOneK Cedos)) hC1two
  set C1 := stepOneC1 d Cedos Cann Citer (stepOneK Cedos) with hC1def
  set A := stepOneSmallnessCoeff cstar with hAdef
  set B := Real.sqrt (C1⁻¹ * C0) with hBdef
  have hApos : (0 : ℝ) < A := stepOneSmallnessCoeff_pos hcstar
  have hBpos : (0 : ℝ) < B :=
    Real.sqrt_pos.mpr (mul_pos (inv_pos.mpr hC1pos) hC0pos)
  have hABpos : (0 : ℝ) < A * B := mul_pos hApos hBpos
  refine ⟨C1, min (min g0 (Cann⁻¹ * cstar ^ (10 : ℕ)))
      (min (1 / 256) ((A * B / 16) ^ 4)), C0, hC1two,
    two_mul_dim_le_stepOneC1 d Cedos Cann Citer (stepOneK Cedos),
    step6_le_stepOneC1 d Cedos Cann Citer (stepOneK Cedos), ?_, ?_, hC0pos, ?_⟩
  · refine lt_min (lt_min hg0pos ?_) (lt_min (by norm_num) (by positivity))
    exact mul_pos (inv_pos.mpr hCannpos) (pow_pos hcstar 10)
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  intro M hcs hgamma alpha halpha0 halpha
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg0le : M.gamma ≤ g0 :=
    le_trans hgamma (le_trans (min_le_left _ _) (min_le_left _ _))
  have hgreg : M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    rw [hcs]
    exact le_trans hgamma (le_trans (min_le_left _ _) (min_le_right _ _))
  have hg256 : M.gamma ≤ 1 / 256 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgthr : M.gamma ≤ (A * B / 16) ^ 4 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_right _ _))
  have halphaC : C0 * Real.sqrt M.gamma ≤ 1 - alpha := by linarith only [halpha]
  have halpha1 : alpha < 1 := by
    have h : 0 < C0 * Real.sqrt M.gamma :=
      mul_pos hC0pos (Real.sqrt_pos.mpr hgpos)
    linarith only [halpha, h]
  have hdelta : stepOneDelta C1 alpha ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    stepOneDelta_mem hC1two halpha0 halpha1
  have hthr : 16 * Real.sqrt (Real.sqrt M.gamma) ≤ A * B :=
    smallness_threshold (le_of_lt hABpos) hgthr
  have hsmall : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
        stepOneEp (stepOneDelta C1 alpha) := by
    rw [hcs]
    exact stepOne_annular_smallness hgpos (by linarith only [hg256]) hcstar hC1pos
      (le_of_lt hC0pos) halphaC hthr
  have hd0 : stepOneDelta C1 alpha ≤ stepOneDelta0 Cedos Cann (stepOneK Cedos) :=
    stepOneDelta_le_stepOneDelta0 hCedos0 hCannpos halpha0
      (delta0Floor_le_stepOneC1 d Cedos Cann Citer (stepOneK Cedos))
  have hdisp : Cann * stepOneEp (stepOneDelta C1 alpha) ≤
      1 / 2 * Real.rpow stepOneS (3 / 2 : ℝ) * Cedos⁻¹ *
        Real.rpow (3 : ℝ) (-(stepOneK Cedos : ℝ) / 4) :=
    annularCapEighth_le_display hCedos0 (le_of_lt hCannpos)
      (sqrt_stepOneDelta_mul_le hCedos0 hCannpos hd0)
  refine ⟨hdelta, hsmall, ?_, hRG1 M hcs hg0le alpha halpha0 halpha⟩
  intro j z
  filter_upwards [hcap M hgreg hg256 (stepOneDelta C1 alpha) hdelta hsmall j z]
    with omega homega
  exact stepOneEpsJ_le_of_le homega hdisp

/-- **'s Step-2 package at the Step-1 parameters** (frontier item 3).

`step_two_minimalScaleX` was proved with `k` and `C₁` abstract, so its produced
constant read `C(d, c⋆, k, C₁)`. -/
theorem step_two_minimalScaleX_stepOne (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar)
    (Cedos Citer : ℝ) (hCedos : 1 ≤ Cedos) :
    ∃ C1 gamma0 C : ℝ, 2 ≤ C1 ∧ 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ Z : Cutoff.CutoffSample d → ℕ∞,
            Measurable Z ∧
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m → Z omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha)
                  stepOneSEighth_pos n m omega) ∧
            Measurable (minimalScaleX Z (stepOneK Cedos)) ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure
                    {omega | (N : ℕ∞) ≤ minimalScaleX Z (stepOneK Cedos) omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n : ℤ, n ≤ m →
                minimalScaleX Z (stepOneK Cedos) omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                GoodScaleWindows M stepOneSEighth (stepOneDelta C1 alpha)
                  stepOneSEighth_pos n m omega := by
  obtain ⟨C1, gamma0, C, hC1, _, _, hg0, _, hC, hweb⟩ :=
    stepOne_parameterWeb d cstar hcstar Cedos Citer hCedos
  refine ⟨C1, gamma0, C, hC1, hg0, hC, ?_⟩
  intro M hcs hgamma alpha halpha0 halpha
  exact (hweb M hcs hgamma alpha halpha0 halpha).2.2.2

end Algsuperdiff.Section4.Provider.Regularity
