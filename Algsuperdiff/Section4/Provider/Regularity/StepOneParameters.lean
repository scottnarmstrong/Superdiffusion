/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section3.Provider.Diffusivity.FlowArithmetic
import Algsuperdiff.Section4.Provider.Regularity.MinimalScaleShift
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `t.regularity` Step 1: the parameter web `(k, s, δ)`, the `C₁`-largeness
# demands, and the pins

## The target

```
k := ⌈4 log₃ (2 s^{-3/2} C_{e.excess.decay.one.step})⌉ ,   s := 1/4 ,
δ := C₁⁻¹(1 - α) ,                          C₁ = C₁(d, c⋆) large enough.
```

The excess-decay one-step constant is NOT yet fixed anywhere in the repository,
so it is carried here as the abstract real `Cedos`; every statement below is
uniform in it.

## Contents

* `stepOneKArg`, `stepOneK` — the printed `k`, and `stepOneKArg_eq`, the
  evaluation `2 s^{-3/2} C = 16 C` at `s = 1/4`.  The ceiling is `Nat.ceil`
  because the source says `k ∈ ℕ`; at `C_edos ≥ 1` the argument of the
  logarithm exceeds `1`, so `Nat.ceil` and `Int.ceil` agree there.
* `stepOneDelta0`, `stepOneC1Delta0`, `stepOneDelta_le_stepOneDelta0`,
  `sqrt_stepOneDelta_mul_le` — the third Step-1 bullet: the threshold `δ₀` with
  `δ₀^{1/2} s^{-1/2} C_edos C_ann ≤ ½ 3^{-k/4}`, and the explicit `C₁`-floor
  that forces `δ ≤ δ₀`.
* `stepOneEp`, `annularCap_le_display`, `annularCapEighth_le_display` — the
  good-event threshold `⅛ s δ^{1/2}` and the Step-1 `ε_j(z)` display.
* `thirteen_le_minimalScaleX`, `thirteen_le_window`,
  `StepOneBadSetSeparation` — the pins.

## Deviations from the printed text

1. The printed first bullet reads `γ|log γ|² ≤ s c⋆² (⅛ s δ^{1/2})` with the
   Step-1 `s = 1/4` in the first slot.  The annular producer is applied at the
   index `s/8` (that is the index inside `𝒢(j, z; ⅛s, ⅛ s δ^{1/2})` and inside
   `ε_j(z)`), so the honest requirement is at `(s/8)^{3/2}`; that is the form
   discharged here and in `StepOneEpsilon.lean`.  Both differ from the print by
   a fixed numerical factor only (`s` is the numeral `1/4`).
2. `s^{-3/2}`, `s^{3/2}` and `3^{-k/4}` are written with `Real.rpow`, as the
   frozen theorems do; the only numeral evaluated is `Real.rpow (1/4) (3/2) =
   1/8`.  `3^{-k/4}` is kept opaque (only positivity and `Real.rpow_neg` are used),
   so no transcendental atom ever reaches a numeric tactic.

## References

* ABK26, `t.regularity` Step 1.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

/-! ## 1. The `s`-powers at the Step-1 numeral `s = 1/4` -/

/-- `s = 1/4`. -/
theorem stepOneS_eq : stepOneS = 1 / 4 := rfl

/-- `0 < s`. -/
theorem stepOneS_pos : 0 < stepOneS := by
  rw [stepOneS_eq]
  norm_num

/-- `s/8 ≤ s`. -/
theorem stepOneSEighth_le_stepOneS : stepOneSEighth ≤ stepOneS := by
  rw [stepOneSEighth_eq, stepOneS_eq]
  norm_num

/-- `√s = 1/2`. -/
theorem sqrt_stepOneS : Real.sqrt stepOneS = 1 / 2 := by
  rw [stepOneS_eq, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]

/-- `s^{3/2} = 1/8` at `s = 1/4`. -/
theorem stepOneS_rpow_three_halves : Real.rpow stepOneS (3 / 2 : ℝ) = 1 / 8 := by
  rw [stepOneS_eq]
  show (1 / 4 : ℝ) ^ (3 / 2 : ℝ) = 1 / 8
  have h2 : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
    rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]
  have h : (1 / 4 : ℝ) ^ (3 / 2 : ℝ) = ((1 / 4 : ℝ) ^ (1 / 2 : ℝ)) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast ((1 / 4 : ℝ) ^ (1 / 2 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 4)]
    norm_num
  rw [h, h2]
  norm_num

/-- `s^{-3/2} = 8` at `s = 1/4`. -/
theorem stepOneS_rpow_neg_three_halves : Real.rpow stepOneS (-(3 / 2) : ℝ) = 8 := by
  have h : Real.rpow stepOneS (-(3 / 2) : ℝ) = (Real.rpow stepOneS (3 / 2 : ℝ))⁻¹ :=
    Real.rpow_neg (by rw [stepOneS_eq]; norm_num) _
  rw [h, stepOneS_rpow_three_halves]
  norm_num

/-! ## 2. The Step-1 integer `k`, and the pin -/

/-- The argument of the logarithm in `e.parameter.choices.regularity`: `2 s^{-3/2}
C_{e.excess.decay.one.step}`.  `Cedos` is the abstract excess-decay one-step
constant. -/
noncomputable def stepOneKArg (Cedos : ℝ) : ℝ :=
  2 * Real.rpow stepOneS (-(3 / 2) : ℝ) * Cedos

/-- `k := ⌈4 log₃ (2 s^{-3/2} C_{e.excess.decay.one.step})⌉` of
`e.parameter.choices.regularity`, as a function of the abstract excess-decay
one-step constant. -/
noncomputable def stepOneK (Cedos : ℝ) : ℕ := ⌈4 * Real.logb 3 (stepOneKArg Cedos)⌉₊

/-- `2 s^{-3/2} C = 16 C` at the Step-1 numeral `s = 1/4`. -/
theorem stepOneKArg_eq (Cedos : ℝ) : stepOneKArg Cedos = 16 * Cedos := by
  rw [stepOneKArg, stepOneS_rpow_neg_three_halves]
  ring

/-- **The pin, discharged.**  `10 ≤ k` for every `C_edos ≥ 1`.

It is a consequence of the printed formula for `k` as soon as `16 C_edos ≥
3^{5/2}`, and `3^{5/2} = √243 < 16`, so the explicit floor `1 ≤ C_edos`
suffices. -/
theorem stepOneK_ge_ten {Cedos : ℝ} (hCedos : 1 ≤ Cedos) : 10 ≤ stepOneK Cedos := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : Real.log ((3:ℝ) ^ (5:ℕ)) ≤ Real.log ((16:ℝ) ^ (2:ℕ)) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h1
  push_cast at h1
  have h52 : (5:ℝ) / 2 ≤ Real.logb 3 16 := by
    rw [Real.logb, le_div_iff₀ hlog3]
    linarith only [h1]
  have hmono : Real.logb 3 16 ≤ Real.logb 3 (16 * Cedos) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num)
      (by linarith only [hCedos])
  have hten : (10:ℝ) ≤ 4 * Real.logb 3 (stepOneKArg Cedos) := by
    rw [stepOneKArg_eq]
    linarith only [h52, hmono]
  have hceil : 4 * Real.logb 3 (stepOneKArg Cedos) ≤
      ((⌈4 * Real.logb 3 (stepOneKArg Cedos)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hR : (10:ℝ) ≤ ((stepOneK Cedos : ℕ) : ℝ) := by
    rw [stepOneK]
    linarith only [hten, hceil]
  exact_mod_cast hR

/-! ## 3. The factor `3^{k/4}` -/

/-- `3^{k/4}`, the factor of the third Step-1 bullet, kept opaque. -/
noncomputable def stepOneThreePow (k : ℕ) : ℝ := Real.rpow (3 : ℝ) ((k : ℝ) / 4)

/-- `0 < 3^{k/4}`. -/
theorem stepOneThreePow_pos (k : ℕ) : 0 < stepOneThreePow k :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- `3^{-k/4} = (3^{k/4})⁻¹`. -/
theorem rpow_three_neg_quarter (k : ℕ) :
    Real.rpow (3 : ℝ) (-(k : ℝ) / 4) = (stepOneThreePow k)⁻¹ := by
  rw [neg_div, stepOneThreePow]
  exact Real.rpow_neg (by norm_num) _

/-- `0 < 3^{-k/4}`. -/
theorem rpow_three_neg_quarter_pos (k : ℕ) : 0 < Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := by
  rw [rpow_three_neg_quarter]
  exact inv_pos.mpr (stepOneThreePow_pos k)

/-! ## 4. The third Step-1 bullet: `δ ≤ δ₀` -/

/-- `δ₀` of the third Step-1 bullet: the largest tolerance with `δ₀^{1/2} s^{-1/2}
C_edos C_ann ≤ ½ 3^{-k/4}`, here taken with equality. -/
noncomputable def stepOneDelta0 (Cedos Cann : ℝ) (k : ℕ) : ℝ :=
  (Real.sqrt stepOneS * (2 * Cedos * Cann * stepOneThreePow k)⁻¹) ^ 2

/-- `0 < δ₀`. -/
theorem stepOneDelta0_pos {Cedos Cann : ℝ} (hCedos : 0 < Cedos) (hCann : 0 < Cann)
    (k : ℕ) : 0 < stepOneDelta0 Cedos Cann k := by
  have hden : (0:ℝ) < 2 * Cedos * Cann * stepOneThreePow k :=
    mul_pos (mul_pos (mul_pos (by norm_num) hCedos) hCann) (stepOneThreePow_pos k)
  have hbase : (0:ℝ) < Real.sqrt stepOneS * (2 * Cedos * Cann * stepOneThreePow k)⁻¹ := by
    rw [sqrt_stepOneS]
    exact mul_pos (by norm_num) (inv_pos.mpr hden)
  exact pow_pos hbase 2

/-- **The defining property of `δ₀`**: `δ₀^{1/2} s^{-1/2} C_edos C_ann = ½
3^{-k/4}`. -/
theorem sqrt_stepOneDelta0_mul {Cedos Cann : ℝ} (hCedos : 0 < Cedos) (hCann : 0 < Cann)
    (k : ℕ) :
    Real.sqrt (stepOneDelta0 Cedos Cann k) * (Real.sqrt stepOneS)⁻¹ * Cedos * Cann =
      1 / 2 * Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := by
  have hT : (0:ℝ) < stepOneThreePow k := stepOneThreePow_pos k
  have hden : (0:ℝ) < 2 * Cedos * Cann * stepOneThreePow k :=
    mul_pos (mul_pos (mul_pos (by norm_num) hCedos) hCann) hT
  have hbase : (0:ℝ) ≤ Real.sqrt stepOneS * (2 * Cedos * Cann * stepOneThreePow k)⁻¹ := by
    rw [sqrt_stepOneS]
    exact le_of_lt (mul_pos (by norm_num) (inv_pos.mpr hden))
  have hCe : Cedos ≠ 0 := ne_of_gt hCedos
  have hCa : Cann ≠ 0 := ne_of_gt hCann
  have hTne : stepOneThreePow k ≠ 0 := ne_of_gt hT
  rw [stepOneDelta0, Real.sqrt_sq hbase, rpow_three_neg_quarter, sqrt_stepOneS]
  field_simp

/-- The `C₁`-floor of the largeness condition: `C₁ ≥ δ₀⁻¹` forces `δ = C₁⁻¹(1-α) ≤
δ₀`. -/
noncomputable def stepOneC1Delta0 (Cedos Cann : ℝ) (k : ℕ) : ℝ :=
  (stepOneDelta0 Cedos Cann k)⁻¹

/-- **The third Step-1 bullet, at the explicit `C₁`-floor**: `δ ≤ δ₀`. -/
theorem stepOneDelta_le_stepOneDelta0 {Cedos Cann C1 alpha : ℝ} {k : ℕ}
    (hCedos : 0 < Cedos) (hCann : 0 < Cann) (halpha0 : 0 < alpha)
    (hC1 : stepOneC1Delta0 Cedos Cann k ≤ C1) :
    stepOneDelta C1 alpha ≤ stepOneDelta0 Cedos Cann k := by
  have hd0 : (0:ℝ) < stepOneDelta0 Cedos Cann k := stepOneDelta0_pos hCedos hCann k
  have hinv0 : (0:ℝ) < (stepOneDelta0 Cedos Cann k)⁻¹ := inv_pos.mpr hd0
  have hC1pos : (0:ℝ) < C1 := lt_of_lt_of_le hinv0 (by rwa [stepOneC1Delta0] at hC1)
  have hmul : (1:ℝ) ≤ stepOneDelta0 Cedos Cann k * C1 := by
    calc (1:ℝ) = stepOneDelta0 Cedos Cann k * (stepOneDelta0 Cedos Cann k)⁻¹ :=
          (mul_inv_cancel₀ (ne_of_gt hd0)).symm
      _ ≤ stepOneDelta0 Cedos Cann k * C1 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hd0)
          rwa [stepOneC1Delta0] at hC1
  have hstep : C1⁻¹ ≤ stepOneDelta0 Cedos Cann k := by
    have h := mul_le_mul_of_nonneg_right hmul (le_of_lt (inv_pos.mpr hC1pos))
    rwa [one_mul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hC1pos), mul_one] at h
  calc stepOneDelta C1 alpha = C1⁻¹ * (1 - alpha) := rfl
    _ ≤ C1⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith only [halpha0])
          (le_of_lt (inv_pos.mpr hC1pos))
    _ = C1⁻¹ := mul_one _
    _ ≤ stepOneDelta0 Cedos Cann k := hstep

/-- **The third Step-1 bullet, in the form the `ε_j(z)` display consumes**:
`δ^{1/2} s^{-1/2} C_edos C_ann ≤ ½ 3^{-k/4}`. -/
theorem sqrt_stepOneDelta_mul_le {Cedos Cann delta : ℝ} {k : ℕ} (hCedos : 0 < Cedos)
    (hCann : 0 < Cann) (hdelta : delta ≤ stepOneDelta0 Cedos Cann k) :
    Real.sqrt delta * (Real.sqrt stepOneS)⁻¹ * Cedos * Cann ≤
      1 / 2 * Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := by
  have hcoef : (0:ℝ) ≤ (Real.sqrt stepOneS)⁻¹ := by
    rw [sqrt_stepOneS]
    norm_num
  have hsq : Real.sqrt delta ≤ Real.sqrt (stepOneDelta0 Cedos Cann k) :=
    Real.sqrt_le_sqrt hdelta
  calc Real.sqrt delta * (Real.sqrt stepOneS)⁻¹ * Cedos * Cann
      ≤ Real.sqrt (stepOneDelta0 Cedos Cann k) * (Real.sqrt stepOneS)⁻¹ * Cedos * Cann := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (le_of_lt hCedos))
          (le_of_lt hCann)
        exact mul_le_mul_of_nonneg_right hsq hcoef
    _ = 1 / 2 * Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := sqrt_stepOneDelta0_mul hCedos hCann k

/-! ## 5. The four largeness demands on `C₁` -/

/-- **The Step-1 constant `C₁`**, as the maximum of the largeness demands: the
`δ`-window pin `C₁ ≥ 2` of `p.minimal.scale.separation.sec4`, the Step-7
volume/transport pins `C₁ ≥ 2d` and `C₁ ≥ 2(d + γ)` (`γ ≤ 1` in the regime),
the Step-6 demand `C₁ ≥ 4 C_iter (k+1)/log 3`, and the `δ₀` threshold of the
third bullet.  `Citer` is the abstract Step-6 iteration constant, `Cann` the
annular one, `Cedos` the excess-decay one-step one; all three depend only on
`d`, so `C₁ = C₁(d)` — inside the printed `C₁ = C₁(d, c⋆)`. -/
noncomputable def stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) : ℝ :=
  max (max 2 (2 * (d : ℝ) + 2))
    (max (4 * Citer * ((k : ℝ) + 1) / Real.log 3) (stepOneC1Delta0 Cedos Cann k))

/-- pin: `C₁ ≥ 2`, the pin that puts `δ = C₁⁻¹(1-α)` inside the `(0,1/2]` window of
`p.minimal.scale.separation.sec4`. -/
theorem two_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    2 ≤ stepOneC1 d Cedos Cann Citer k :=
  le_trans (le_max_left _ _) (le_max_left _ _)

/-- pins (3) and (4): `C₁ ≥ 2d`, and `C₁ ≥ 2(d + γ)` whenever `γ ≤ 1` — the Step-7
volume factor `3^{(d/2)(n'-n)}` and the coarse-graining transport
`3^{(1/2)(d+γ)(m-m')}`. -/
theorem two_mul_dim_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    2 * (d : ℝ) + 2 ≤ stepOneC1 d Cedos Cann Citer k :=
  le_trans (le_max_right _ _) (le_max_left _ _)

/-- pin (4) in the form Step 7 reads it: `2(d + γ) ≤ C₁` for `γ ≤ 1`. -/
theorem two_mul_dim_add_gamma_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ)
    {gamma : ℝ} (hgamma : gamma ≤ 1) :
    2 * ((d : ℝ) + gamma) ≤ stepOneC1 d Cedos Cann Citer k := by
  have h := two_mul_dim_le_stepOneC1 d Cedos Cann Citer k
  linarith only [h, hgamma]

/-- pin (2): `C₁ ≥ 4 C_iter (k+1)/log 3`, the Step-6 demand. -/
theorem step6_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ stepOneC1 d Cedos Cann Citer k :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- pin (1): `C₁ ≥ δ₀⁻¹`, the third bullet's threshold. -/
theorem delta0Floor_le_stepOneC1 (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    stepOneC1Delta0 Cedos Cann k ≤ stepOneC1 d Cedos Cann Citer k :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- `0 < C₁`. -/
theorem stepOneC1_pos (d : ℕ) (Cedos Cann Citer : ℝ) (k : ℕ) :
    0 < stepOneC1 d Cedos Cann Citer k :=
  lt_of_lt_of_le (by norm_num) (two_le_stepOneC1 d Cedos Cann Citer k)

/-! ## 6. The good-event threshold `⅛ s δ^{1/2}` and the `ε_j(z)` display -/

/-- The Step-1 good-event threshold `⅛ s δ^{1/2}`, which is also the threshold `s'
√δ` of `p.minimal.scale.separation.sec4` at the Step-1 slot `s' = s/8`. -/
noncomputable def stepOneEp (delta : ℝ) : ℝ := stepOneSEighth * Real.sqrt delta

/-- `⅛ s δ^{1/2} ∈ (0, 1/2]`: the `ε`-range of the annular producer's clause (ii). -/
theorem stepOneEp_mem_Ioc {delta : ℝ} (hdelta : delta ∈ Set.Ioc (0:ℝ) (1 / 2)) :
    stepOneEp delta ∈ Set.Ioc (0:ℝ) (1 / 2) := by
  have hpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta.1
  have hle : Real.sqrt delta ≤ 1 := by
    have h := Real.sqrt_le_sqrt (le_trans hdelta.2 (by norm_num : (1/2:ℝ) ≤ 1))
    rwa [Real.sqrt_one] at h
  have hval : stepOneEp delta = 1 / 32 * Real.sqrt delta := by
    rw [stepOneEp, stepOneSEighth_eq]
  rw [hval]
  exact ⟨mul_pos (by norm_num) hpos, by linarith only [hle]⟩

/-- The good-event threshold is below the printed cap slot: `⅛ s δ^{1/2} ≤ s
δ^{1/2}`. -/
theorem stepOneEp_le_stepOneS_mul (delta : ℝ) :
    stepOneEp delta ≤ stepOneS * Real.sqrt delta :=
  mul_le_mul_of_nonneg_right stepOneSEighth_le_stepOneS (Real.sqrt_nonneg delta)

/-- **The Step-1 `ε_j(z)` display, scalar half**: the annular cap `C_ann s δ^{1/2}`
is below `½ s^{3/2} C_edos⁻¹ 3^{-k/4}` exactly when the third bullet holds.
The hypothesis is `sqrt_stepOneDelta_mul_le`'s conclusion. -/
theorem annularCap_le_display {Cedos Cann delta : ℝ} {k : ℕ} (hCedos : 0 < Cedos)
    (h : Real.sqrt delta * (Real.sqrt stepOneS)⁻¹ * Cedos * Cann ≤
      1 / 2 * Real.rpow (3 : ℝ) (-(k : ℝ) / 4)) :
    Cann * (stepOneS * Real.sqrt delta) ≤
      1 / 2 * Real.rpow stepOneS (3 / 2 : ℝ) * Cedos⁻¹ *
        Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := by
  have hinv : (0:ℝ) < Cedos⁻¹ := inv_pos.mpr hCedos
  rw [sqrt_stepOneS, show ((1:ℝ) / 2)⁻¹ = 2 by norm_num] at h
  have h' : 2 * (Cedos * (Cann * Real.sqrt delta)) ≤
      1 / 2 * Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := by
    linarith only [h]
  have hX : Cann * Real.sqrt delta ≤
      1 / 4 * (Cedos⁻¹ * Real.rpow (3 : ℝ) (-(k : ℝ) / 4)) := by
    have hmul := mul_le_mul_of_nonneg_left h' (le_of_lt hinv)
    have hl : Cedos⁻¹ * (2 * (Cedos * (Cann * Real.sqrt delta))) =
        2 * (Cann * Real.sqrt delta) := by
      field_simp
    rw [hl] at hmul
    linarith only [hmul]
  rw [stepOneS_rpow_three_halves, stepOneS_eq]
  calc Cann * (1 / 4 * Real.sqrt delta) = 1 / 4 * (Cann * Real.sqrt delta) := by ring
    _ ≤ 1 / 4 * (1 / 4 * (Cedos⁻¹ * Real.rpow (3 : ℝ) (-(k : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_left hX (by norm_num)
    _ = 1 / 2 * (1 / 8) * Cedos⁻¹ * Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := by ring

/-- **The Step-1 `ε_j(z)` display at the good-event threshold `⅛ s δ^{1/2}`.** This
is the form the annular cap actually produces: `C_ann · (⅛ s δ^{1/2})`, which
is below the printed `C_ann s δ^{1/2}` and hence below the display value. -/
theorem annularCapEighth_le_display {Cedos Cann delta : ℝ} {k : ℕ} (hCedos : 0 < Cedos)
    (hCann : 0 ≤ Cann)
    (h : Real.sqrt delta * (Real.sqrt stepOneS)⁻¹ * Cedos * Cann ≤
      1 / 2 * Real.rpow (3 : ℝ) (-(k : ℝ) / 4)) :
    Cann * stepOneEp delta ≤
      1 / 2 * Real.rpow stepOneS (3 / 2 : ℝ) * Cedos⁻¹ *
        Real.rpow (3 : ℝ) (-(k : ℝ) / 4) := by
  refine le_trans ?_ (annularCap_le_display hCedos h)
  refine mul_le_mul_of_nonneg_left ?_ hCann
  rw [stepOneEp]
  exact mul_le_mul_of_nonneg_right stepOneSEighth_le_stepOneS
    (Real.sqrt_nonneg delta)

/-! ## 7. The first bullet's arithmetic: `γ |log γ|²` against `δ^{1/2}` -/

/-- **The `γ|log γ|²` smallness, abstract-real form.**  With `u := √(√γ)`, the
proved bound `γ|log γ|² ≤ 16 √γ = 16 u²` turns the smallness demand into the
single linear condition `16 u ≤ A B`.  No transcendental atom reaches a numeric
tactic: `Real.log` is touched only through the imported bound. -/
theorem gammaLogSq_le_of_sqrt_sqrt_le {g A B : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hu : 16 * Real.sqrt (Real.sqrt g) ≤ A * B) :
    g * |Real.log g| ^ 2 ≤ A * (B * Real.sqrt (Real.sqrt g)) := by
  have hu0 : (0:ℝ) ≤ Real.sqrt (Real.sqrt g) := Real.sqrt_nonneg _
  have hbase := Algsuperdiff.Section3.Provider.Diffusivity.mul_sq_abs_log_le hg0 hg1
  refine le_trans hbase ?_
  calc 16 * Real.sqrt g
      = 16 * Real.sqrt (Real.sqrt g) * Real.sqrt (Real.sqrt g) := by
        rw [mul_assoc, Real.mul_self_sqrt (Real.sqrt_nonneg g)]
    _ ≤ A * B * Real.sqrt (Real.sqrt g) := mul_le_mul_of_nonneg_right hu hu0
    _ = A * (B * Real.sqrt (Real.sqrt g)) := by ring

/-- **The lower bound on `δ^{1/2}` supplied by the theorem's own `α`-range.** From
`α ≤ 1 - C γ^{1/2}` one gets `δ = C₁⁻¹(1-α) ≥ C₁⁻¹ C γ^{1/2}`, hence `δ^{1/2} ≥
(C₁⁻¹C)^{1/2} · √(√γ)`.  This is the S Step-1 bullet read as a lower bound on
`δ`, and it is what makes the first bullet's discharge possible uniformly in
`α`. -/
theorem sqrt_stepOneDelta_ge {C1 C g alpha : ℝ} (hC1 : 0 < C1) (hC : 0 ≤ C)
    (halpha : C * Real.sqrt g ≤ 1 - alpha) :
    Real.sqrt (C1⁻¹ * C) * Real.sqrt (Real.sqrt g) ≤
      Real.sqrt (stepOneDelta C1 alpha) := by
  have h1 : C1⁻¹ * (C * Real.sqrt g) ≤ stepOneDelta C1 alpha :=
    mul_le_mul_of_nonneg_left halpha (le_of_lt (inv_pos.mpr hC1))
  have h2 : Real.sqrt (C1⁻¹ * (C * Real.sqrt g)) ≤ Real.sqrt (stepOneDelta C1 alpha) :=
    Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt (C1⁻¹ * (C * Real.sqrt g)) =
      Real.sqrt (C1⁻¹ * C) * Real.sqrt (Real.sqrt g) := by
    rw [← mul_assoc,
      Real.sqrt_mul (mul_nonneg (le_of_lt (inv_pos.mpr hC1)) hC) (Real.sqrt g)]
  rwa [h3] at h2

/-! ## 8. The second Step-1 bullet, as printed -/

/-- **The second Step-1 bullet's printed equivalence**: the demand `δ ≥ K` of
`p.minimal.scale.separation.sec4` reads, at `δ = C₁⁻¹(1-α)`, as `1 - α ≥ C₁ K`.
With `K = C s^{-7/2} c⋆⁻¹ γ^{1/2}` this is the printed "equivalent to `1 - α ≥₁
c⋆⁻¹ γ^{1/2}`". -/
theorem le_stepOneDelta_iff {C1 K alpha : ℝ} (hC1 : 0 < C1) :
    K ≤ stepOneDelta C1 alpha ↔ C1 * K ≤ 1 - alpha := by
  rw [stepOneDelta]
  constructor
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hC1)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hC1), one_mul] at h2
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hC1))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC1), one_mul] at h2

/-- **The second Step-1 bullet, discharged from the theorem's own hypothesis.**

The theorem's `α ≤ 1 - C γ^{1/2}` gives `δ ≥ C_b γ^{1/2}` for every `C_b` with
`C₁ C_b ≤ C`; that is the reconciliation of the printed bullet with the
constant produced by `step_two_minimalScaleX` (whose `stepTwoConst` carries the
same demand in its squared, `γ`-gate form). -/
theorem stepOneDelta_ge_of_alpha {C1 Cb C g alpha : ℝ} (hC1 : 0 < C1)
    (hCb : C1 * Cb ≤ C) (halpha : C * Real.sqrt g ≤ 1 - alpha) :
    Cb * Real.sqrt g ≤ stepOneDelta C1 alpha := by
  rw [le_stepOneDelta_iff hC1]
  have h : C1 * Cb * Real.sqrt g ≤ C * Real.sqrt g :=
    mul_le_mul_of_nonneg_right hCb (Real.sqrt_nonneg g)
  calc C1 * (Cb * Real.sqrt g) = C1 * Cb * Real.sqrt g := by ring
    _ ≤ C * Real.sqrt g := h
    _ ≤ 1 - alpha := halpha

/-! ## 9. The pins -/

/-- **The Step-7 window-length pin **: `X_m(α) = Z_m + k + 3 ≥ 13` whenever `k ≥
10`. -/
theorem thirteen_le_minimalScaleX {Omega : Type*} (Z : Omega → ℕ∞) {k : ℕ}
    (hk : 10 ≤ k) (omega : Omega) : (13 : ℕ∞) ≤ minimalScaleX Z k omega := by
  rw [minimalScaleX_eq_add_cast]
  have h : ((13 : ℕ) : ℕ∞) ≤ ((k + 3 : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
  calc (13 : ℕ∞) = ((13 : ℕ) : ℕ∞) := by norm_num
    _ ≤ ((k + 3 : ℕ) : ℕ∞) := h
    _ ≤ Z omega + ((k + 3 : ℕ) : ℕ∞) := le_add_self

/-- **The window-length demand the Step-1 pins impose on the consumer**: at `k ≥
10`, the gate `X_m(α) ≤ m - n` of Steps 3--7 is available only on windows of
length at least 13. -/
theorem thirteen_le_window {Omega : Type*} (Z : Omega → ℕ∞) {k : ℕ} (hk : 10 ≤ k)
    (omega : Omega) {n m : ℤ} (hgate : minimalScaleX Z k omega ≤ (((m - n).toNat : ℕ) : ℕ∞)) :
    (13 : ℤ) ≤ m - n := by
  have h13 : ((13 : ℕ) : ℕ∞) ≤ (((m - n).toNat : ℕ) : ℕ∞) := by
    refine le_trans ?_ (le_trans (thirteen_le_minimalScaleX Z hk omega) hgate)
    norm_num
  have hnat : 13 ≤ (m - n).toNat := Nat.cast_le.mp h13
  omega

/-- **The separation side condition**, recorded as a named demand for the windows and
bad-set step: the number of bad scales in the window plus 7 must not exceed the window
length. It resolves the `n' = m'` reading by supplying exactly this condition; it is a
presentational gap in the manuscript, NOT discharged here — the bad set is not formed in
this module. -/
def StepOneBadSetSeparation (badCard : ℕ) (n m : ℤ) : Prop :=
  (badCard : ℤ) + 7 ≤ m - n

/-- The separation demand in the `ℕ`-form a bad-set cardinality bound produces. -/
theorem stepOneBadSetSeparation_of_le {badCard : ℕ} {n m : ℤ}
    (h : badCard + 7 ≤ (m - n).toNat) : StepOneBadSetSeparation badCard n m := by
  rw [StepOneBadSetSeparation]
  omega

end Algsuperdiff.Section4.Provider.Regularity
