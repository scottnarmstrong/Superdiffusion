/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineCzGridDepthTest

/-!
# The EXACT size of the far-band half: `min(j·log 3, (s·p')^{-1})`

## Why

`HomSpineCzGridDepthTest` §4 records the far half of the single-depth
boundary-layer estimate as the truncated geometric sum
`Σ_{i<j} 3^{-i·s·p'}`, proves it `≥ j/3` on the window `j·s·p' ≤ 1`, and
proves it UNBOUNDED over the admissible `(s, j)` range.  That leaves open the
size at a FIXED order — the quantity this development actually pays, since the
Step-3 pin fixes `s ≍ |log γ|^{-1}` and then lets `j` run to `10|log γ|`.

This file closes the arithmetic with a two-sided bound.  Writing `x = s·p'`:

```text
  min( j/3, (2/(3 log 3))·x^{-1} )  ≤  Σ_{i<j} 3^{-x i}  ≤  (1 - 3^{-x})^{-1}
```

(`farBand_sum_ge_min`, `farBand_sum_le_geom`), and the right side is itself
`≤ (x log 3)^{-1}·(1-3^{-x})^{-1}(1-3^{-x})`, i.e. of the same `x^{-1}` order —
so the far half is `≍ min(j, x^{-1})`, saturating at `x^{-1}` once `j ≥ x^{-1}`
(`farBand_sum_ge_inv_of_one_le_mul`).

Consequence for the surviving route (the DEPTH-level converse, the
per-cell one having been refuted in `HomSpineSupFormCellRefuted`): the constant
the single-depth Gagliardo input can carry is
`Cg^{p'} ≍ C(d) + min(j·log 3, (s·p')^{-1})`, hence at the Step-3 pin
`CA ≍ |log γ|^{1/p'}` — NOT `γ`-uniform, and the deficit is exactly the
Gagliardo-vs-Besov (Bourgain--Brezis--Mironescu) constant of the test space as
`s → 0`.  This file proves the arithmetic; the identification with `Cg` is
The `fullENorm_gridDualDepthTest_le_of_gagliardo` slot and is NOT claimed
here.
-/

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

/-- The far-band sum in closed form. -/
private theorem geom_sum_three_rpow {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ))) =
      (1 - (3 : ℝ) ^ (-x * (j : ℝ))) / (1 - (3 : ℝ) ^ (-x)) := by
  have hrlt : (3 : ℝ) ^ (-x) < 1 := three_rpow_neg_lt_one hx
  have hpow : ∀ i : ℕ, (3 : ℝ) ^ (-x * (i : ℝ)) = ((3 : ℝ) ^ (-x)) ^ i := by
    intro i
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-x)) i,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [Finset.sum_congr rfl (fun i _ => hpow i),
    geom_sum_eq (by linarith only [hrlt] : (3 : ℝ) ^ (-x) ≠ 1), hpow j,
    div_eq_div_iff (by linarith only [hrlt] : (3 : ℝ) ^ (-x) - 1 ≠ 0)
      (by linarith only [hrlt] : 1 - (3 : ℝ) ^ (-x) ≠ 0)]
  ring

/-- **The far half is at most the full geometric sum** `(1-3^{-x})^{-1}`: at a
fixed order the band sum saturates, it does not grow with the depth. -/
theorem farBand_sum_le_geom {x : ℝ} (hx : 0 < x) (j : ℕ) :
    (∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ))) ≤ (1 - (3 : ℝ) ^ (-x))⁻¹ := by
  have hrlt : (3 : ℝ) ^ (-x) < 1 := three_rpow_neg_lt_one hx
  have hden : 0 < 1 - (3 : ℝ) ^ (-x) := by linarith only [hrlt]
  have hnum : 1 - (3 : ℝ) ^ (-x * (j : ℝ)) ≤ 1 := by
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (-x * (j : ℝ)) := three_rpow_pos _
    linarith only [hpos]
  rw [geom_sum_three_rpow hx j]
  calc (1 - (3 : ℝ) ^ (-x * (j : ℝ))) / (1 - (3 : ℝ) ^ (-x))
      = (1 - (3 : ℝ) ^ (-x * (j : ℝ))) * (1 - (3 : ℝ) ^ (-x))⁻¹ := div_eq_mul_inv _ _
    _ ≤ 1 * (1 - (3 : ℝ) ^ (-x))⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
    _ = (1 - (3 : ℝ) ^ (-x))⁻¹ := one_mul _

/-- **The far half saturates at `x^{-1}`.**  Once the depth reaches the order's
own window (`x·j ≥ 1`) the far bands already sum to at least
`(2/(3 log 3))·x^{-1}` — no `j`, no `d`, and unbounded as `x = s·p' → 0`.

This is the quantitative form of the negative finding: at the Step-3 pin
`s ≍ |log γ|^{-1}` and depths up to `10|log γ|` the far half is `≳ |log γ|`. -/
theorem farBand_sum_ge_inv_of_one_le_mul {x : ℝ} (hx : 0 < x) {j : ℕ}
    (hj : 1 ≤ x * (j : ℝ)) :
    2 / (3 * Real.log 3) * x⁻¹ ≤ ∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ)) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrlt : (3 : ℝ) ^ (-x) < 1 := three_rpow_neg_lt_one hx
  have hden : 0 < 1 - (3 : ℝ) ^ (-x) := by linarith only [hrlt]
  have hupper : 1 - (3 : ℝ) ^ (-x) ≤ x * Real.log 3 := by
    have hbase := Real.add_one_le_exp (Real.log 3 * (-x))
    have hrw : (3 : ℝ) ^ (-x) = Real.exp (Real.log 3 * (-x)) :=
      Real.rpow_def_of_pos (by norm_num) _
    rw [hrw]
    linarith only [hbase]
  have hnum : (3 : ℝ) ^ (-x * (j : ℝ)) ≤ 1 / 3 := by
    have hmono : (3 : ℝ) ^ (-x * (j : ℝ)) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hj])
    have hval : (3 : ℝ) ^ (-1 : ℝ) = 1 / 3 := by
      rw [Real.rpow_neg_one]
      norm_num
    rwa [hval] at hmono
  have hxl : 0 < x * Real.log 3 := mul_pos hx hlog
  have hrw : 2 / (3 * Real.log 3) * x⁻¹ = (2 / 3 : ℝ) * (x * Real.log 3)⁻¹ := by
    field_simp
  have hinv : (x * Real.log 3)⁻¹ ≤ (1 - (3 : ℝ) ^ (-x))⁻¹ := inv_anti₀ hden hupper
  have step1 : (2 / 3 : ℝ) * (x * Real.log 3)⁻¹ ≤
      (2 / 3 : ℝ) * (1 - (3 : ℝ) ^ (-x))⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  have step2 : (2 / 3 : ℝ) * (1 - (3 : ℝ) ^ (-x))⁻¹ ≤
      (1 - (3 : ℝ) ^ (-x * (j : ℝ))) * (1 - (3 : ℝ) ^ (-x))⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith only [hnum]) (inv_nonneg.mpr hden.le)
  rw [geom_sum_three_rpow hx j]
  calc 2 / (3 * Real.log 3) * x⁻¹
      = (2 / 3 : ℝ) * (x * Real.log 3)⁻¹ := hrw
    _ ≤ (2 / 3 : ℝ) * (1 - (3 : ℝ) ^ (-x))⁻¹ := step1
    _ ≤ (1 - (3 : ℝ) ^ (-x * (j : ℝ))) * (1 - (3 : ℝ) ^ (-x))⁻¹ := step2
    _ = (1 - (3 : ℝ) ^ (-x * (j : ℝ))) / (1 - (3 : ℝ) ^ (-x)) := (div_eq_mul_inv _ _).symm

/-- **THE TWO-SIDED SIZE OF THE FAR HALF.**  Below the order's window the far
bands grow linearly in the depth; above it they saturate at `x^{-1}`.  Together
with `farBand_sum_le_geom` this pins the far half at `≍ min(j, x^{-1})`. -/
theorem farBand_sum_ge_min {x : ℝ} (hx : 0 < x) (j : ℕ) :
    min ((j : ℝ) / 3) (2 / (3 * Real.log 3) * x⁻¹) ≤
      ∑ i ∈ Finset.range j, (3 : ℝ) ^ (-x * (i : ℝ)) := by
  rcases le_or_gt (x * (j : ℝ)) 1 with hle | hgt
  · exact le_trans (min_le_left _ _) (farBand_sum_ge_of_mul_le_one hx.le j hle)
  · exact le_trans (min_le_right _ _) (farBand_sum_ge_inv_of_one_le_mul hx hgt.le)

end

end Algsuperdiff.Section4.Provider.Homogenization
