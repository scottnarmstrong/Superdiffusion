/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSixHolderExponent

namespace Algsuperdiff.Section4.Provider.Regularity

noncomputable section

/-! ## 1. The print's `t e^t ≤ e^{2t}` -/

/-- **`t e^t ≤ e^{2t}`** for `t ≥ 0` -- the print's absorption of a polynomial
prefactor into its own exponential.  The only input is `x ≤ x + 1 ≤ e^x`. -/
theorem mul_exp_le_exp_two_mul {a : ℝ} (ha : 0 ≤ a) :
    a * Real.exp a ≤ Real.exp (2 * a) := by
  have h1 : a ≤ Real.exp a :=
    le_trans (by linarith only [ha] : a ≤ a + 1) (Real.add_one_le_exp a)
  have h2 : a * Real.exp a ≤ Real.exp a * Real.exp a :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos a).le
  have h3 : Real.exp a * Real.exp a = Real.exp (2 * a) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : 0 ≤ a * Real.exp a := mul_nonneg ha (Real.exp_pos a).le
  linarith only [h2, h3, h4]

/-- `3^x = exp((log 3) x)`; the single place `rpow` and `exp` meet in this module. -/
theorem rpow_three_eq_exp (x : ℝ) : Real.rpow (3 : ℝ) x = Real.exp (Real.log 3 * x) :=
  Real.rpow_def_of_pos (by norm_num) x

/-- **The absorption in `3`-powers**: for every `t ≥ 0`,

```text
   t · 3^{(1/4) t}  ≤  (4 / log 3) · 3^{(1/2) t} .
``` -/
theorem mul_rpow_three_quarter_le (t : ℝ) (ht : 0 ≤ t) :
    t * Real.rpow (3 : ℝ) (1 / 4 * t) ≤ 4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * t) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha : 0 ≤ Real.log 3 / 4 * t := mul_nonneg (by linarith only [hlog]) ht
  have hq : Real.rpow (3 : ℝ) (1 / 4 * t) = Real.exp (Real.log 3 / 4 * t) := by
    rw [rpow_three_eq_exp]
    congr 1
    ring
  have hh : Real.rpow (3 : ℝ) (1 / 2 * t) = Real.exp (2 * (Real.log 3 / 4 * t)) := by
    rw [rpow_three_eq_exp]
    congr 1
    ring
  have ht' : t = 4 / Real.log 3 * (Real.log 3 / 4 * t) := by
    field_simp
  have habs := mul_exp_le_exp_two_mul ha
  have hpos : (0 : ℝ) ≤ 4 / Real.log 3 := div_nonneg (by norm_num) hlog.le
  have hmul := mul_le_mul_of_nonneg_left habs hpos
  rw [hq, hh]
  nth_rewrite 1 [ht']
  calc 4 / Real.log 3 * (Real.log 3 / 4 * t) * Real.exp (Real.log 3 / 4 * t)
      = 4 / Real.log 3 * ((Real.log 3 / 4 * t) * Real.exp (Real.log 3 / 4 * t)) := by ring
    _ ≤ 4 / Real.log 3 * Real.exp (2 * (Real.log 3 / 4 * t)) := hmul

/-! ## 2. The `ε`-funded flat leg: the print's absorption, `α`-free -/

/-- **The printed absorption**, at the abstract reals.

If the flat `∇h` leg enters the `δ`-budget multiplied by the `ε`-sum -- i.e. with
the coefficient `S ≤ 2 C₁^{-1} t`, which `e.sum.eps.j.bound` supplies with `t =
(1-α)(m-n)` -- then

```text
   exp( C₁^{-1} C_iter t ) · S · H  ≤  (8 / (C₁ log 3)) · 3^{(1/2) t} · H .
```

The constant carries NO `α`, NO `γ` and NO `δ`: the coefficient IS the
exponent's own argument, which is precisely why the print's `t e^t ≤ e^{2t}`
step is free. -/
theorem stepSixFlat_epsFunded_absorb {C1 Citer t S H : ℝ} {k : ℕ} (hC1 : 0 < C1)
    (hCiter : 0 ≤ Citer) (ht : 0 ≤ t) (hS0 : 0 ≤ S) (hH : 0 ≤ H)
    (hfloor : 4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ C1)
    (hS : S ≤ 2 * (C1⁻¹ * t)) :
    Real.exp (C1⁻¹ * Citer * t) * (S * H) ≤
      8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) * H := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hexp : Real.exp (C1⁻¹ * Citer * t) ≤ Real.rpow (3 : ℝ) (1 / 4 * t) :=
    exp_le_rpow_three_quarter_of_step6_floor (k := k) hC1 hCiter ht hfloor
  have hqnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 4 * t) := Real.rpow_nonneg (by norm_num) _
  have h1 : Real.exp (C1⁻¹ * Citer * t) * S ≤ Real.rpow (3 : ℝ) (1 / 4 * t) * (2 * (C1⁻¹ * t)) := by
    have ha := mul_le_mul_of_nonneg_right hexp hS0
    have hb := mul_le_mul_of_nonneg_left hS hqnn
    linarith only [ha, hb]
  have h2 : Real.rpow (3 : ℝ) (1 / 4 * t) * (2 * (C1⁻¹ * t)) =
      2 * C1⁻¹ * (t * Real.rpow (3 : ℝ) (1 / 4 * t)) := by ring
  have h3 : (0 : ℝ) ≤ 2 * C1⁻¹ := by
    have : (0 : ℝ) ≤ C1⁻¹ := (inv_pos.mpr hC1).le
    linarith only [this]
  have h4 := mul_le_mul_of_nonneg_left (mul_rpow_three_quarter_le t ht) h3
  have h5 : 2 * C1⁻¹ * (4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * t)) =
      8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) := by
    field_simp
    ring
  have h6 : Real.exp (C1⁻¹ * Citer * t) * S ≤
      8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) := by
    linarith only [h1, h2, h4, h5]
  have h7 := mul_le_mul_of_nonneg_right h6 hH
  calc Real.exp (C1⁻¹ * Citer * t) * (S * H)
      = Real.exp (C1⁻¹ * Citer * t) * S * H := by ring
    _ ≤ 8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) * H := h7

/-- **The print's absorption at the development's own `C₁` and `ε`-budget.**

At `C₁ = stepOne d ...` (whose pin gives `C₁ ≥ 2` and Step 6's floor) and the
printed `ε`-sum `2 δ (m-n)` with `δ = C₁^{-1}(1-α)`, the coefficient IS `2
C₁^{-1} (1-α)(m-n) = 2 C₁^{-1} · stepSixExponent`, and the absorbed leg is

```text
   exp( C₁^{-1} C_iter (1-α)(m-n) ) · 2 δ (m-n) · H
     ≤  (4 / log 3) · 3^{(1/2)(1-α)(m-n)} · H ,
```

an ABSOLUTE constant. -/
theorem stepSixFlat_epsFunded_absorb_stepOneC1 (d : ℕ) {Cedos Cann Citer alpha H : ℝ}
    {k : ℕ} {n m : ℤ} (hCiter : 0 ≤ Citer) (halpha : alpha ≤ 1) (hnm : n ≤ m)
    (hH : 0 ≤ H) :
    Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
        (2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha * ((m : ℝ) - (n : ℝ)) * H) ≤
      4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * H := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hC1 : 0 < stepOneC1 d Cedos Cann Citer k := stepOneC1_pos d Cedos Cann Citer k
  have hC12 : (2 : ℝ) ≤ stepOneC1 d Cedos Cann Citer k := two_le_stepOneC1 d Cedos Cann Citer k
  have ht : 0 ≤ stepSixExponent alpha n m := stepSixExponent_nonneg halpha hnm
  have hSeq : 2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha * ((m : ℝ) - (n : ℝ)) =
      2 * ((stepOneC1 d Cedos Cann Citer k)⁻¹ * stepSixExponent alpha n m) := by
    simp only [stepOneDelta, stepSixExponent]
    ring
  have hS0 : 0 ≤ 2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
      ((m : ℝ) - (n : ℝ)) := by
    rw [hSeq]
    exact mul_nonneg (by norm_num) (mul_nonneg (inv_pos.mpr hC1).le ht)
  have habs := stepSixFlat_epsFunded_absorb (k := k) hC1 hCiter ht hS0 hH
    (step6_le_stepOneC1 d Cedos Cann Citer k) (le_of_eq hSeq)
  have hconst : 8 / (stepOneC1 d Cedos Cann Citer k * Real.log 3) ≤ 4 / Real.log 3 := by
    rw [div_le_div_iff₀ (mul_pos hC1 hlog) hlog]
    have h := mul_le_mul_of_nonneg_right hC12 hlog.le
    linarith only [h]
  have hRnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * H :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hH
  have hmono := mul_le_mul_of_nonneg_right hconst hRnn
  calc Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
        (2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha * ((m : ℝ) - (n : ℝ)) * H)
      ≤ 8 / (stepOneC1 d Cedos Cann Citer k * Real.log 3) *
          Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * H := habs
    _ ≤ 4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * H := by
        linarith only [hmono]

/-! ## 3. The `ε`-free flat leg: the best available bound, and its sharpness -/

/-- **The `ε`-free flat leg's price.**  With the bare window count `(m-n)` in
place of the `ε`-budget `2 δ (m-n)`, the same absorption produces

```text
   exp( C₁^{-1} C_iter (1-α)(m-n) ) · (m-n) · H
     ≤  (4 / ((1-α) log 3)) · 3^{(1/2)(1-α)(m-n)} · H ,
```

with the factor `(1-α)^{-1}` -- i.e. `C₁ δ^{-1}`, and `≤ C γ^{-1/2}` in the
printed range `1-α ≥ C(d,c⋆) γ^{1/2}`.  `epsFree_flat_price_sharp` shows this
factor cannot be removed. -/
theorem stepSixFlat_epsFree_price (d : ℕ) {Cedos Cann Citer alpha H : ℝ} {k : ℕ}
    {n m : ℤ} (hCiter : 0 ≤ Citer) (halpha : alpha < 1) (hnm : n ≤ m) (hH : 0 ≤ H) :
    Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
        (((m : ℝ) - (n : ℝ)) * H) ≤
      4 / ((1 - alpha) * Real.log 3) *
        Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * H := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hC1 : 0 < stepOneC1 d Cedos Cann Citer k := stepOneC1_pos d Cedos Cann Citer k
  have ha0 : 0 < 1 - alpha := by linarith only [halpha]
  have ht : 0 ≤ stepSixExponent alpha n m :=
    stepSixExponent_nonneg (le_of_lt halpha) hnm
  have hexp : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
      stepSixExponent alpha n m) ≤
      Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    exp_stepOneC1_le_rpow_three_quarter d hCiter (le_of_lt halpha) hnm
  have hqnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    Real.rpow_nonneg (by norm_num) _
  have hmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : ((n : ℝ)) ≤ ((m : ℝ)) := Int.cast_le.mpr hnm
    linarith only [this]
  have heq : (m : ℝ) - (n : ℝ) = (1 - alpha)⁻¹ * stepSixExponent alpha n m := by
    simp only [stepSixExponent]
    field_simp
  have h1 : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
      ((m : ℝ) - (n : ℝ)) ≤
      Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) * ((m : ℝ) - (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hexp hmn
  have h2 : Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) * ((m : ℝ) - (n : ℝ)) =
      (1 - alpha)⁻¹ *
        (stepSixExponent alpha n m * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m)) := by
    rw [heq]; ring
  have h3 : (0 : ℝ) ≤ (1 - alpha)⁻¹ := (inv_pos.mpr ha0).le
  have h4 := mul_le_mul_of_nonneg_left (mul_rpow_three_quarter_le _ ht) h3
  have h5 : (1 - alpha)⁻¹ * (4 / Real.log 3 *
        Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m)) =
      4 / ((1 - alpha) * Real.log 3) *
        Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) := by
    field_simp
  have h6 : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
      ((m : ℝ) - (n : ℝ)) ≤
      4 / ((1 - alpha) * Real.log 3) *
        Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) := by
    linarith only [h1, h2, h4, h5]
  have h7 := mul_le_mul_of_nonneg_right h6 hH
  calc Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
        (((m : ℝ) - (n : ℝ)) * H)
      = Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
          ((m : ℝ) - (n : ℝ)) * H := by ring
    _ ≤ 4 / ((1 - alpha) * Real.log 3) *
          Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * H := h7

/-- `3^{1/2} ≤ 2`. -/
theorem rpow_three_half_le_two : Real.rpow (3 : ℝ) (1 / 2 : ℝ) ≤ 2 := by
  have h : Real.rpow (3 : ℝ) (1 / 2 : ℝ) = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
  have h4 : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
  have h2 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  linarith only [h, h4, h2]

/-- **The sharpness of the `(1-α)^{-1}` price.**

If a constant `K` dominates the bare window count against the printed exponent,

```text
   N  ≤  K · 3^{(1/2)(1-α) N}      for every  N ∈ ℕ ,
```

then `(1-α)^{-1} - 1 ≤ 2 K`.  Hence NO `α`-free constant closes the `ε`-free
flat sum at the printed display: the cost is exactly `Θ((1-α)^{-1})`, i.e.
`Θ(δ^{-1})`, i.e. `Θ(γ^{-1/2})` in the printed `α`-range. -/
theorem epsFree_flat_price_sharp {alpha K : ℝ} (ha0 : 0 < 1 - alpha)
    (hK : ∀ N : ℕ, (N : ℝ) ≤ K * Real.rpow (3 : ℝ) (1 / 2 * ((1 - alpha) * (N : ℝ)))) :
    (1 - alpha)⁻¹ - 1 ≤ 2 * K := by
  have hK0 : 0 ≤ K := by
    have h := hK 0
    simp only [Nat.cast_zero, mul_zero] at h
    have hz : Real.rpow (3 : ℝ) 0 = 1 := Real.rpow_zero 3
    rw [hz, mul_one] at h
    linarith only [h]
  set N : ℕ := ⌊(1 - alpha)⁻¹⌋₊ with hN_def
  have hinv0 : 0 ≤ (1 - alpha)⁻¹ := (inv_pos.mpr ha0).le
  have hNle : (N : ℝ) ≤ (1 - alpha)⁻¹ := Nat.floor_le hinv0
  have hprod : (1 - alpha) * (N : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hNle ha0.le
    rw [mul_inv_cancel₀ (ne_of_gt ha0)] at h
    exact h
  have hexple : Real.rpow (3 : ℝ) (1 / 2 * ((1 - alpha) * (N : ℝ))) ≤
      Real.rpow (3 : ℝ) (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hprod])
  have hstep : (N : ℝ) ≤ K * 2 := by
    have h1 := hK N
    have h2 : K * Real.rpow (3 : ℝ) (1 / 2 * ((1 - alpha) * (N : ℝ))) ≤
        K * Real.rpow (3 : ℝ) (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hexple hK0
    have h3 : K * Real.rpow (3 : ℝ) (1 / 2 : ℝ) ≤ K * 2 :=
      mul_le_mul_of_nonneg_left rpow_three_half_le_two hK0
    linarith only [h1, h2, h3]
  have hfloor : (1 - alpha)⁻¹ < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith only [hstep, hfloor]

end

end Algsuperdiff.Section4.Provider.Regularity
