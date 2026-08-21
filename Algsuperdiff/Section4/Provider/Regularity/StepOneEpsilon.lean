/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.GoodEventCaps
import Algsuperdiff.Section4.Provider.Regularity.StepOneParameters

/-!
# `t.regularity` Step 1: the annular-admissibility bullet and `ε_j(z)`

## The target

ABK26 `t.regularity` Step 1, (the first bullet's second half) (the definition
of `ε_j(z)` and its cap):

```
ε_j(z) := 𝓔_{s/8,∞,2}(z + □_j; a_L - (κ_L-κ_j)_{z+□_j}, σ̂_j) · 1_{𝒢(j,z; ⅛s, ⅛ s δ^{1/2})} ,
ε_j(z) ≤ C_{ann} s δ^{1/2} ≤ ½ s^{3/2} C_{edos}^{-1} 3^{-k/4} .
```

## The re-verification (binding)

The printed first bullet asks for `γ|log γ|² ≤ s c⋆² (⅛ s δ^{1/2})`; the frozen
producer is at the strengthened hypothesis `γ|log γ|² ≤ t^{3/2} c⋆² ε` with `t` the index
at which it is applied.  Step 1 applies it at `t = s/8` (that is the index
inside `𝒢(j,z; ⅛s, …)` and inside `ε_j(z)`) and at `ε = ⅛ s δ^{1/2}`, so the
honest requirement discharged here is

```
γ |log γ|²  ≤  (s/8)^{3/2} · c⋆² · (⅛ s δ^{1/2}) .
```

The discharge is NOT from `γ ≤ γ₀` alone: `δ` degenerates as `α → 1`, and the
lower bound on `δ` is exactly the theorem's own hypothesis `α ≤ 1 - C(d,c⋆)
γ^{1/2}` (the S Step-1 bullet), through `sqrt_stepOneDelta_ge`.  What survives
is the one-variable condition `16 √(√γ) ≤ A √(C₁⁻¹C)` of
`stepOne_annular_smallness`, met by `γ ≤ (A √(C₁⁻¹C)/16)⁴`.  This is the honest
content of the printed sentence "by the condition `γ ≤ γ₀(d,c⋆)`".

## Contents

* `stepOneEpsJ` — the definition of `ε_j(z)`, in the carriers the frozen
  producers use (`fluxCorrectedErrorObservableSup` at the `z`-translated sample,
  gated by `goodEventAt`, `ℝ≥0∞`-valued).
* `stepOneSEighth_mem_Icc` — the annular `s`-window at `γ ≤ 1/256`.
* `stepOneSmallnessCoeff`, `stepOne_annular_smallness`,
  `sqrt_sqrt_le_of_le_pow_four`, `smallness_threshold` — the arithmetic of the
  admissibility bullet.
* `ae_stepOneEpsJ_le` — **the `ε_j(z)` cap**: `ε_j(z) ≤ C_ann · (⅛ s δ^{1/2})`
  almost surely, for every scale `j` and every centre `z`.
* `stepOneEpsJ_le_of_le` — the cap transported to any larger bound (used at
  the Step-1 display value in `StepOneWeb.lean`).

## Deviations from the printed text

1. **The `∞` slot.**  `ε_j(z)` is formed here with
   `Support.fluxCorrectedErrorObservableSup`, the supremum over the truncation
   levels `L ≥ j` of the flux-corrected `(∞,2)` representative — the object the
   frozen `p.minimal.scale.separation.sec4` and `p.mathcalE.annular.decomp`
   clauses both carry.  It dominates the printed per-`L` representative
   (`Support.le_fluxCorrectedErrorObservableSup`), so the cap proved here is
   stronger than the printed one at every fixed `L`.
2. **The centre.**  The frozen annular clause (ii) is stated at the centre `0`
   and the untranslated sample; the transport to `(z, z`-translated sample`)`
   is the proved law-preserving translation, not a new assumption.
3. **The cap's `ε` slot.**  The printed chain writes `ε_j(z) ≤ C_ann s δ^{1/2}`;
   the producer delivers `C_ann ε` at `ε = ⅛ s δ^{1/2}`, which is smaller.
   Both are below the Step-1 display value (`annularCapEighth_le_display`).

## References

* ABK26, `t.regularity` Step 1.
* ABK26, `e.mathcalE.annular.decomp.good.event`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The annular window at the Step-1 index `s/8` -/

/-- The Step-1 index `s/8 = 1/32` lies in the annular producer's `s`-window `[8γ,
1/4]` as soon as `γ ≤ 1/256`. -/
theorem stepOneSEighth_mem_Icc {gamma : ℝ} (hgamma : gamma ≤ 1 / 256) :
    stepOneSEighth ∈ Set.Icc (8 * gamma) (1 / 4 : ℝ) := by
  rw [stepOneSEighth_eq]
  exact ⟨by linarith only [hgamma], by norm_num⟩

/-! ## 2. The scalar arithmetic of the admissibility bullet -/

/-- The coefficient `A := (s/8)^{3/2} c⋆² (s/8)` of the strengthened annular
smallness hypothesis at the Step-1 slot, so that its right-hand side is `A ·
δ^{1/2}`. -/
noncomputable def stepOneSmallnessCoeff (cstar : ℝ) : ℝ :=
  Real.rpow stepOneSEighth (3 / 2 : ℝ) * cstar ^ (2 : ℕ) * stepOneSEighth

/-- `0 < A`. -/
theorem stepOneSmallnessCoeff_pos {cstar : ℝ} (hcstar : 0 < cstar) :
    0 < stepOneSmallnessCoeff cstar :=
  mul_pos (mul_pos (Real.rpow_pos_of_pos stepOneSEighth_pos _) (pow_pos hcstar 2))
    stepOneSEighth_pos

/-- The right-hand side of the strengthened smallness hypothesis, in the form `A ·
δ^{1/2}`. -/
theorem stepOneSmallness_rhs (cstar delta : ℝ) :
    Real.rpow stepOneSEighth (3 / 2 : ℝ) * cstar ^ (2 : ℕ) * stepOneEp delta =
      stepOneSmallnessCoeff cstar * Real.sqrt delta := by
  rw [stepOneSmallnessCoeff, stepOneEp]
  ring

/-- `√(√g) ≤ t` from `g ≤ t⁴`. -/
theorem sqrt_sqrt_le_of_le_pow_four {g t : ℝ} (ht : 0 ≤ t) (hg : g ≤ t ^ 4) :
    Real.sqrt (Real.sqrt g) ≤ t := by
  have h2 : Real.sqrt (t ^ 4) = t ^ 2 := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (pow_two_nonneg t)]
  have h1 : Real.sqrt g ≤ t ^ 2 := by
    rw [← h2]
    exact Real.sqrt_le_sqrt hg
  have h3 : Real.sqrt (Real.sqrt g) ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq ht] at h3

/-- **The `γ`-threshold of the admissibility bullet**: `γ ≤ (AB/16)⁴` is exactly
what the one-variable condition `16 √(√γ) ≤ A B` needs. -/
theorem smallness_threshold {g A B : ℝ} (hAB : 0 ≤ A * B)
    (hg : g ≤ (A * B / 16) ^ 4) : 16 * Real.sqrt (Real.sqrt g) ≤ A * B := by
  have ht : (0:ℝ) ≤ A * B / 16 := by linarith only [hAB]
  have h := sqrt_sqrt_le_of_le_pow_four ht hg
  linarith only [h]

/-- **The annular-admissibility bullet, scalar form** (at the strengthened
hypothesis).

From the theorem's own `α`-range hypothesis `C γ^{1/2} ≤ 1 - α` and the
one-variable threshold `16 √(√γ) ≤ A √(C₁⁻¹C)`, the smallness demand of the
frozen annular clause (ii) holds at the Step-1 slot `(s/8, ⅛ s δ^{1/2})`. -/
theorem stepOne_annular_smallness {g C1 C alpha cstar : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hcstar : 0 < cstar) (hC1 : 0 < C1) (hC : 0 ≤ C)
    (halpha : C * Real.sqrt g ≤ 1 - alpha)
    (hthr : 16 * Real.sqrt (Real.sqrt g) ≤
      stepOneSmallnessCoeff cstar * Real.sqrt (C1⁻¹ * C)) :
    g * |Real.log g| ^ 2 ≤
      Real.rpow stepOneSEighth (3 / 2 : ℝ) * cstar ^ (2 : ℕ) *
        stepOneEp (stepOneDelta C1 alpha) := by
  have h1 := gammaLogSq_le_of_sqrt_sqrt_le hg0 hg1 hthr
  have h2 := sqrt_stepOneDelta_ge hC1 hC halpha
  rw [stepOneSmallness_rhs]
  exact le_trans h1
    (mul_le_mul_of_nonneg_left h2 (le_of_lt (stepOneSmallnessCoeff_pos hcstar)))

/-! ## 3. `ε_j(z)` -/

/-- **`ε_j(z)`**: the flux-corrected homogenization-error observable at the cube `z
+ □_j` and index `s/8`, restricted to the good event `𝒢(j, z; ⅛ s, ⅛ s
δ^{1/2})`.

The two ingredients are the frozen `d.good.event.for.lambda` carrier
`goodEventAt` and the `d.mathcal.E` carrier `fluxCorrectedErrorObservableSup`,
in exactly the pairing the frozen `p.minimal.scale.separation.sec4` clause uses
(event at the centre `z`, observable at the `z`-translated sample). -/
noncomputable def stepOneEpsJ (M : ABKModel d) (j : ℤ) (z : Vec d) (delta : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  Set.indicator
    (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) j z
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ (stepOneEp delta))
    (fun omega' =>
      Support.fluxCorrectedErrorObservableSup M j ⟨stepOneSEighth, stepOneSEighth_pos⟩
        (Cutoff.translateCutoffSample z omega'))
    omega

/-- **The `ε_j(z)` cap (first inequality)**: almost surely, at every scale `j`
and every centre `z`,

```
ε_j(z) ≤ C_ann · (⅛ s δ^{1/2}) ,
```

The three hypotheses are that anchor's own premises at the Step-1 slot: the
standing regime `γ ≤ C_ann⁻¹ c⋆¹⁰`, the `s`-window (through `γ ≤ 1/256`), the
`ε`-range (through `δ ∈ (0,1/2]`) and the strengthened smallness. -/
theorem ae_stepOneEpsJ_le (d : ℕ) :
    ∃ Cann : ℝ, 0 < Cann ∧
      ∀ M : ABKModel d, M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ 1 / 256 →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ (j : ℤ) (z : Vec d),
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                stepOneEpsJ M j z delta omega ≤
                  ENNReal.ofReal (Cann * stepOneEp delta) := by
  obtain ⟨Cann, hCannpos, hcap⟩ :=
    ExcessDecay.ae_errorObservableSup_le_of_mem_goodEventAt d
  refine ⟨Cann, hCannpos, ?_⟩
  intro M hregime hgamma delta hdelta hsmall j z
  have hslot := hcap M hregime ⟨stepOneSEighth, stepOneSEighth_pos⟩
    (stepOneSEighth_mem_Icc hgamma) (stepOneEp delta) (stepOneEp_mem_Ioc hdelta)
    hsmall j z
  filter_upwards [hslot] with omega homega
  rw [stepOneEpsJ]
  by_cases hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) j z ⟨stepOneSEighth, stepOneSEighth_pos⟩
      (stepOneEp delta)
  · rw [Set.indicator_of_mem hmem]
    exact homega hmem
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le _

/-- Monotonicity of the cap in its right-hand side: the form in which the Step-1
display value replaces the annular one. -/
theorem stepOneEpsJ_le_of_le {M : ABKModel d} {j : ℤ} {z : Vec d} {delta a b : ℝ}
    {omega : Cutoff.CutoffSample d}
    (h : stepOneEpsJ M j z delta omega ≤ ENNReal.ofReal a) (hab : a ≤ b) :
    stepOneEpsJ M j z delta omega ≤ ENNReal.ofReal b :=
  le_trans h (ENNReal.ofReal_le_ofReal hab)

end Algsuperdiff.Section4.Provider.Regularity
