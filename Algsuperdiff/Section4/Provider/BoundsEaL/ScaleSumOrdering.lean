/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Step 5's scale sum: the two orderings of the same per-scale data

Nothing here imports that file, and nothing here claims the anchor.  Everything
below is abstract-real arithmetic: no model, no measure, no carrier occurs.

## What is here

The manuscript's Step 5 combines the per-scale data

```
G_l  =  B · min{1, (γ(D+l))^{1/2}} · 3^{γ(D+l)} ,   D = m − n ,  l = n − j ≥ 0 ,
```

(`B` carries the `Γ₂`-moment constant `(K p)^{1/2}`, `D = m − n`) against the
geometric scale weight `3^{−s l}`.  There are two possible orderings, and they
are NOT equivalent:

* the **`ℓ^p` (Jensen) ordering** `( c_s ∑_l 3^{−s l} G_l^p )^{1/p}`, which is
  what the printed display literally writes -- the weight sits INSIDE the `p`-th
  power, so after the `p`-th root it acts at the rate `s/p`; and
* the **`ℓ¹` (Minkowski) ordering** `( c_{2s} ∑_l 3^{−s l} G_l^2 )^{1/2}`, which
  is what `d.mathcal.E`'s `q = 2` branch offers directly (the scale sum is
  already outside the `p`-th power there, so the `p/2`-th moments may be
  combined by the triangle inequality in `L^{p/2}` instead of by Jensen).

This module proves the exact arithmetic of both.

1. `minkowskiOrder_scaleSum_le` / `sqrt_minkowskiOrder_bound_le`: in the `ℓ¹`
   ordering the sum is at most `γ(36 D + 144/s)`, i.e. its square root is at most
   `12 √γ (√D + s^{−1/2})` -- exactly the value the manuscript's Step 5 asserts
   for its display, with an explicit absolute constant.
2. `anchorScalar_rpow_lt_jensenOrder_weighted_term` (with
   `jensenOrder_term_le_printed_summand` for faithfulness to the printed
   summand): in the `ℓ^p` ordering ONE term of the same sum already exceeds the
   `p`-th power of the anchor's own scalar `C √γ s^{−1}` at `D = 0` and at the
   top `p = C^{-1} γ^{-1} s` of the anchor's `p`-range, for `C > 72`.  Since
   the anchor's statement at a constant `C₀` implies it at every `C ≥ C₀` (all
   three parameter ranges shrink and the right-hand side grows with `C`), this
   settles the `ℓ^p` ordering for every constant.

The two together locate the discrepancy exactly: it is the placement of the
`p`-th root relative to the scale sum, and nothing else.  The maximising scale
in 2 is `l ≈ p/s`, where `3^{−s l/p} ≈ 1/3` while `(γ l)^{1/2} ≈ (γ p/s)^{1/2}`;
the `ℓ¹` ordering instead sees the geometric weight at full strength and is
maximised at `l ≈ 1/s`, which is the source of the printed `s^{−1/2}`.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 5; `d.mathcal.E`;
  `e.mathcalE.infty.to.q`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

/-! ## 1. Two elementary transcendental estimates -/

/-- `1 ≤ log 3`, from `exp 1 < 2.72 < 3`. -/
private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  exact le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))

/-- **The geometric discount is at least `u/2`** on `0 < u ≤ 1`:
`u/2 ≤ 1 − 3^{−u}`.  This is the only place a logarithm enters the `ℓ¹`
ordering. -/
theorem half_le_one_sub_rpow_three_neg {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - (3 : ℝ) ^ (-u) := by
  have hL : (1 : ℝ) ≤ Real.log 3 := one_le_log_three
  have hL0 : (0 : ℝ) < Real.log 3 := lt_of_lt_of_le zero_lt_one hL
  have hXlb : 1 + u * Real.log 3 ≤ (3 : ℝ) ^ u := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hE := Real.add_one_le_exp (Real.log 3 * u)
    have hcomm : Real.log 3 * u = u * Real.log 3 := mul_comm _ _
    linarith only [hE, hcomm]
  have hden : (0 : ℝ) < 1 + u * Real.log 3 := by positivity
  have hX0 : (0 : ℝ) < (3 : ℝ) ^ u := Real.rpow_pos_of_pos (by norm_num) u
  have hinv : ((3 : ℝ) ^ u)⁻¹ ≤ (1 + u * Real.log 3)⁻¹ := by
    exact inv_anti₀ hden hXlb
  have hprod : (1 : ℝ) ≤ Real.log 3 * (2 - u) :=
    le_trans hL (le_mul_of_one_le_right hL0.le (by linarith only [hu1]))
  have hid : (1 - u / 2) * (1 + u * Real.log 3) - 1 =
      u / 2 * (Real.log 3 * (2 - u) - 1) := by ring
  have hnn : 0 ≤ u / 2 * (Real.log 3 * (2 - u) - 1) :=
    mul_nonneg (by linarith only [hu]) (by linarith only [hprod])
  have hle : (1 + u * Real.log 3)⁻¹ ≤ 1 - u / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith only [hid, hnn]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) u]
  linarith only [hinv, hle]

/-- **Bernoulli for base two**: `1 + p/2 ≤ 2^p` for `p ≥ 0`. -/
theorem one_add_half_le_two_rpow {p : ℝ} (hp : 0 ≤ p) : 1 + p / 2 ≤ (2 : ℝ) ^ p := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 :=
    le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hE := Real.add_one_le_exp (Real.log 2 * p)
  have hmul : 1 / 2 * p ≤ Real.log 2 * p := mul_le_mul_of_nonneg_right hlog hp
  linarith only [hE, hmul]

/-! ## 2. The `ℓ¹` (Minkowski) ordering: the manuscript's own value -/

/-- **The scale sum in the `ℓ¹` ordering.**

For `0 < s ≤ 1`, `4γ ≤ s`, `D ≥ 0` and `γ D ≤ 1` (the anchor's own binder
`m ≤ n + γ^{-1}`),

```
(1 − 3^{−2s}) · ∑_{l ≥ 0} 3^{−s l} · γ(D+l) · 3^{2γ(D+l)}  ≤  γ (36 D + 144/s) .
```

The summand is the square of the second summand's per-scale majorant
`min{1,(γ(D+l))^{1/2}} 3^{γ(D+l)}` with the `min` discarded (`min ≤` its second
argument), and the prefactor is the `q = 2` geometric discount `𝔠_{2s}`. -/
theorem minkowskiOrder_scaleSum_le {s gam D : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hgam : 0 ≤ gam) (h4gam : 4 * gam ≤ s) (hD : 0 ≤ D) (hgamD : gam * D ≤ 1) :
    (1 - (3 : ℝ) ^ (-(2 * s))) *
        ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
      gam * (36 * D + 144 / s) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  set r : ℝ := (3 : ℝ) ^ (-(s / 2)) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos h30 _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hw0 : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hrpow : ∀ l : ℕ, r ^ l = (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    intro l
    rw [hrdef, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 2))) l,
      ← Real.rpow_mul h30.le]
  -- the termwise bound
  have hterm : ∀ l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
        9 * gam * (r ^ l * (D + (l : ℝ))) := by
    intro l
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcoef : 0 ≤ gam * (D + (l : ℝ)) := mul_nonneg hgam (by linarith only [hD, hl0])
    have hexp : -(s * (l : ℝ)) + 2 * gam * (D + (l : ℝ)) ≤ 2 + -(s / 2) * (l : ℝ) := by
      have hDpart : 2 * (gam * D) ≤ 2 := by linarith only [hgamD]
      have hlpart : 2 * gam * (l : ℝ) ≤ s / 2 * (l : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [h4gam]) hl0
      have hexpand : 2 * gam * (D + (l : ℝ)) = 2 * (gam * D) + 2 * gam * (l : ℝ) := by
        ring
      have hsl : 0 ≤ s * (l : ℝ) := mul_nonneg hs.le hl0
      linarith only [hDpart, hlpart, hexpand, hsl]
    have hpow : (3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) ≤
        9 * r ^ l := by
      rw [← Real.rpow_add h30]
      calc (3 : ℝ) ^ (-(s * (l : ℝ)) + 2 * gam * (D + (l : ℝ)))
          ≤ (3 : ℝ) ^ (2 + -(s / 2) * (l : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = 9 * r ^ l := by
            rw [Real.rpow_add h30, hrpow l]
            norm_num
    calc (3 : ℝ) ^ (-(s * (l : ℝ))) *
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))
        = gam * (D + (l : ℝ)) *
            ((3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by ring
      _ ≤ gam * (D + (l : ℝ)) * (9 * r ^ l) := mul_le_mul_of_nonneg_left hpow hcoef
      _ = 9 * gam * (r ^ l * (D + (l : ℝ))) := by ring
  -- summability
  have hsumG : Summable fun l : ℕ => r ^ l := summable_geometric_of_lt_one hr0.le hr1
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hsumL : Summable fun l : ℕ => (l : ℝ) * r ^ l := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    exact h.congr fun l => by rw [pow_one]
  have hsumR : Summable fun l : ℕ => 9 * gam * (r ^ l * (D + (l : ℝ))) := by
    refine ((hsumG.mul_left (9 * gam * D)).add (hsumL.mul_left (9 * gam))).congr ?_
    intro l
    ring
  have hsumLHS : Summable fun l : ℕ => (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by
    refine hsumR.of_nonneg_of_le (fun l => ?_) hterm
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcoef : 0 ≤ gam * (D + (l : ℝ)) := mul_nonneg hgam (by linarith only [hD, hl0])
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (l : ℝ))) := Real.rpow_nonneg h30.le _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) := Real.rpow_nonneg h30.le _
    exact mul_nonneg h1 (mul_nonneg hcoef h2)
  -- the two geometric evaluations
  have hgeo : ∑' l : ℕ, r ^ l = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0.le hr1
  have hlin : ∑' l : ℕ, (l : ℝ) * r ^ l = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsplit : ∑' l : ℕ, 9 * gam * (r ^ l * (D + (l : ℝ))) =
      9 * gam * D * (1 - r)⁻¹ + 9 * gam * (r / (1 - r) ^ 2) := by
    have hcongr : ∀ l : ℕ, 9 * gam * (r ^ l * (D + (l : ℝ))) =
        9 * gam * D * r ^ l + 9 * gam * ((l : ℝ) * r ^ l) := by
      intro l
      ring
    rw [tsum_congr hcongr, Summable.tsum_add (hsumG.mul_left (9 * gam * D))
      (hsumL.mul_left (9 * gam)), tsum_mul_left, tsum_mul_left, hgeo, hlin]
  -- the arithmetic of the two geometric constants
  have hr4 : (3 : ℝ) ^ (-(2 * s)) = r ^ 4 := by
    rw [hrpow 4, show -(s / 2) * ((4 : ℕ) : ℝ) = -(2 * s) from by push_cast; ring]
  have hcss : 1 - (3 : ℝ) ^ (-(2 * s)) ≤ 4 * (1 - r) := by
    have h2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have h3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have hpoly : 1 - r ^ 4 = (1 - r) * (1 + r + r ^ 2 + r ^ 3) := by ring
    have hchain : (1 - r) * (1 + r + r ^ 2 + r ^ 3) ≤ (1 - r) * 4 :=
      mul_le_mul_of_nonneg_left (by linarith only [hr1, h2, h3]) hw0.le
    rw [hr4]
    linarith only [hpoly, hchain]
  have hwlb : s / 4 ≤ 1 - r := by
    have h := half_le_one_sub_rpow_three_neg (u := s / 2) (by linarith only [hs])
      (by linarith only [hs1])
    rw [hrdef]
    linarith only [h]
  have hinvw : (1 - r)⁻¹ ≤ 4 / s := by
    rw [le_div_iff₀ hs, inv_mul_eq_div, div_le_iff₀ hw0]
    linarith only [hwlb]
  -- assembly
  have hTle : ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
        9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹)) := by
    refine le_trans (Summable.tsum_le_tsum hterm hsumLHS hsumR) ?_
    rw [hsplit]
    have hsq : r / (1 - r) ^ 2 ≤ (1 - r)⁻¹ * (1 - r)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have hid : (1 - r)⁻¹ * (1 - r)⁻¹ * (1 - r) ^ 2 = 1 := by
        field_simp
      linarith only [hid, hr1.le]
    have hfac : 9 * gam * (r / (1 - r) ^ 2) ≤ 9 * gam * ((1 - r)⁻¹ * (1 - r)⁻¹) :=
      mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 9 * gam by linarith only [hgam])
    have hexpand : 9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹)) =
        9 * gam * D * (1 - r)⁻¹ + 9 * gam * ((1 - r)⁻¹ * (1 - r)⁻¹) := by ring
    linarith only [hfac, hexpand]
  have hTnn : (0 : ℝ) ≤ ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by
    refine tsum_nonneg fun l => ?_
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcoef : 0 ≤ gam * (D + (l : ℝ)) := mul_nonneg hgam (by linarith only [hD, hl0])
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (l : ℝ))) := Real.rpow_nonneg h30.le _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) := Real.rpow_nonneg h30.le _
    exact mul_nonneg h1 (mul_nonneg hcoef h2)
  have hcss0 : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-(2 * s)) := by
    rw [hr4]
    have h4 : r ^ 4 ≤ 1 := pow_le_one₀ hr0.le hr1.le
    linarith only [h4]
  have hstep1 : (1 - (3 : ℝ) ^ (-(2 * s))) *
      ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
        (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
      (4 * (1 - r)) * (9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹))) := by
    refine mul_le_mul hcss hTle hTnn ?_
    positivity
  have hcancel : (4 * (1 - r)) * (9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹))) =
      36 * gam * (D + (1 - r)⁻¹) := by
    field_simp
    ring
  have hfinal : 36 * gam * (D + (1 - r)⁻¹) ≤ gam * (36 * D + 144 / s) := by
    have hmono : (0 : ℝ) ≤ 36 * gam := by linarith only [hgam]
    have hstep : 36 * gam * (D + (1 - r)⁻¹) ≤ 36 * gam * (D + 4 / s) :=
      mul_le_mul_of_nonneg_left (by linarith only [hinvw]) hmono
    have hid : 36 * gam * (D + 4 / s) = gam * (36 * D + 144 / s) := by
      field_simp
      ring
    linarith only [hstep, hid]
  linarith only [hstep1, hcancel, hfinal]

/-- **The `ℓ¹` ordering, after the square root**: the bound of
`minkowskiOrder_scaleSum_le` is at most `12 √γ (√D + s^{−1/2})`, which is the
manuscript's asserted value `C γ^{1/2}(s^{−1/2} + (m−n)^{1/2})` for its Step-5
display with the absolute constant `12`. -/
theorem sqrt_minkowskiOrder_bound_le {s gam D : ℝ} (hs : 0 < s) (hgam : 0 ≤ gam)
    (hD : 0 ≤ D) :
    Real.sqrt (gam * (36 * D + 144 / s)) ≤
      12 * Real.sqrt gam * (Real.sqrt D + (Real.sqrt s)⁻¹) := by
  have hsplit : gam * (36 * D + 144 / s) = 36 * (gam * D) + 144 * (gam / s) := by
    field_simp
  have hsub : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
    intro x y hx hy
    have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    have hcross : 0 ≤ 2 * (Real.sqrt x * Real.sqrt y) := by positivity
    have hexpand : (Real.sqrt x + Real.sqrt y) ^ 2 =
        Real.sqrt x ^ 2 + Real.sqrt y ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by ring
    have hle : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
      linarith only [hx2, hy2, hcross, hexpand]
    refine le_trans (Real.sqrt_le_sqrt hle) (le_of_eq ?_)
    exact Real.sqrt_sq (by positivity)
  have hA : Real.sqrt (36 * (gam * D)) = 6 * (Real.sqrt gam * Real.sqrt D) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hgam,
      show (36 : ℝ) = 6 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  have hB : Real.sqrt (144 * (gam / s)) = 12 * (Real.sqrt gam * (Real.sqrt s)⁻¹) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_div hgam,
      show (144 : ℝ) = 12 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num),
      div_eq_mul_inv]
  have hnnA : (0 : ℝ) ≤ 36 * (gam * D) := by positivity
  have hnnB : (0 : ℝ) ≤ 144 * (gam / s) := by
    have : (0 : ℝ) ≤ gam / s := div_nonneg hgam hs.le
    linarith only [this]
  have hchain := hsub (36 * (gam * D)) (144 * (gam / s)) hnnA hnnB
  rw [hsplit]
  rw [hA, hB] at hchain
  have hgam0 : (0 : ℝ) ≤ Real.sqrt gam := Real.sqrt_nonneg gam
  have hD0 : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hs0 : (0 : ℝ) ≤ (Real.sqrt s)⁻¹ := by positivity
  have hexpand : 12 * Real.sqrt gam * (Real.sqrt D + (Real.sqrt s)⁻¹) =
      12 * (Real.sqrt gam * Real.sqrt D) + 12 * (Real.sqrt gam * (Real.sqrt s)⁻¹) := by
    ring
  have hmid : 6 * (Real.sqrt gam * Real.sqrt D) ≤ 12 * (Real.sqrt gam * Real.sqrt D) := by
    have : (0 : ℝ) ≤ Real.sqrt gam * Real.sqrt D := mul_nonneg hgam0 hD0
    linarith only [this]
  linarith only [hchain, hexpand, hmid]

/-! ## 3. The `ℓ^p` (Jensen) ordering: one term already overshoots -/

/-- Faithfulness to the printed summand: at `γ k ≤ 1` the term used in
`anchorScalar_rpow_lt_jensenOrder_weighted_term` is at most the manuscript's
own summand `3^{−s k} min{1,(γ k)^{p/2}} 3^{p γ k}` (at `D = 0`). -/
theorem jensenOrder_term_le_printed_summand {s gam p : ℝ} {k : ℕ} (hp : 0 ≤ p)
    (hgam : 0 ≤ gam) (hgk : gam * (k : ℝ) ≤ 1) :
    (3 : ℝ) ^ (-(s * (k : ℝ))) * (gam * (k : ℝ)) ^ (p / 2) ≤
      (3 : ℝ) ^ (-(s * (k : ℝ))) *
        (min 1 ((gam * (k : ℝ)) ^ (p / 2)) * (3 : ℝ) ^ (p * gam * (k : ℝ))) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hgk0 : (0 : ℝ) ≤ gam * (k : ℝ) := mul_nonneg hgam hk0
  have hmin : min 1 ((gam * (k : ℝ)) ^ (p / 2)) = (gam * (k : ℝ)) ^ (p / 2) :=
    min_eq_right (Real.rpow_le_one hgk0 hgk (by linarith only [hp]))
  have hexp : (0 : ℝ) ≤ p * gam * (k : ℝ) := mul_nonneg (mul_nonneg hp hgam) hk0
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (p * gam * (k : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num) hexp
    rw [Real.rpow_zero] at h
    exact h
  have hval : (0 : ℝ) ≤ (gam * (k : ℝ)) ^ (p / 2) := Real.rpow_nonneg hgk0 _
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (k : ℝ))) := Real.rpow_nonneg (by norm_num) _
  rw [hmin]
  refine mul_le_mul_of_nonneg_left ?_ hw
  exact le_mul_of_one_le_right hval hone

/-- **One term of the `ℓ^p`-ordered scale sum exceeds the anchor's own scalar.**

Fix `C > 72`, `0 < γ` with `2Cγ ≤ 1`, `s` with `C² √γ ≤ s ≤ 1`, take `p` at the
TOP `C^{-1} γ^{-1} s` of the anchor's `p`-range and `D = m − n = 0`, and let `k`
be any index with `C^{-1}γ^{-1} − 1 ≤ k ≤ C^{-1}γ^{-1}` (e.g. `⌊C^{-1}γ^{-1}⌋`,
which is the maximising scale `l ≈ p/s`).  Then already the single term

```
𝔠_s · 3^{−s k} (γ k)^{p/2}
```

of the `ℓ^p`-ordered weighted sum is strictly larger than the `p`-th power of the
anchor's own scalar `C √γ s^{-1}`, where `𝔠_s = 1 − 3^{−s}` is the geometric
discount.  Since all terms of the sum are nonnegative, the `ℓ^p`-ordered sum
exceeds that scalar too.

The margin is `√C/(6√2)` per unit before the `p`-th power, so it grows with `C`;
`C > 72` is where it first exceeds `1`. -/
theorem anchorScalar_rpow_lt_jensenOrder_weighted_term {C gam s p : ℝ} {k : ℕ}
    (hC : 72 < C) (hgam : 0 < gam) (hCgam : 2 * C * gam ≤ 1)
    (hs : C ^ 2 * Real.sqrt gam ≤ s) (hs1 : s ≤ 1)
    (hp : p = C⁻¹ * gam⁻¹ * s) (hk : (k : ℝ) ≤ C⁻¹ * gam⁻¹)
    (hk' : C⁻¹ * gam⁻¹ - 1 ≤ (k : ℝ)) :
    (C * Real.sqrt gam * s⁻¹) ^ p <
      (1 - (3 : ℝ) ^ (-s)) *
        ((3 : ℝ) ^ (-(s * (k : ℝ))) * (gam * (k : ℝ)) ^ (p / 2)) := by
  have hC0 : (0 : ℝ) < C := by linarith only [hC]
  have hsq0 : (0 : ℝ) < Real.sqrt gam := Real.sqrt_pos.mpr hgam
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs
  have hp0 : (0 : ℝ) < p := by
    rw [hp]
    positivity
  -- the anchor's scalar at `D = 0`
  have hA : C * Real.sqrt gam * s⁻¹ ≤ C⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hs (le_of_lt (inv_pos.mpr hC0))
    have hid : C⁻¹ * (C ^ 2 * Real.sqrt gam) = C * Real.sqrt gam := by
      field_simp
    have h1 : C * Real.sqrt gam ≤ C⁻¹ * s := by linarith only [h, hid]
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hs0))
    have hid2 : C⁻¹ * s * s⁻¹ = C⁻¹ := by
      field_simp
    linarith only [h2, hid2]
  -- (b) the geometric weight at the maximising scale, after the `p`-th root
  have hsk : s * (k : ℝ) ≤ p := by
    have h := mul_le_mul_of_nonneg_left hk hs0.le
    have hid : s * (C⁻¹ * gam⁻¹) = C⁻¹ * gam⁻¹ * s := by ring
    linarith only [h, hid, hp.symm.le, hp.le]
  have hB : (3 : ℝ)⁻¹ ≤ (3 : ℝ) ^ (-(s * (k : ℝ)) / p) := by
    have hdiv : s * (k : ℝ) / p ≤ 1 := (div_le_one hp0).mpr hsk
    have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
      (show (-1 : ℝ) ≤ -(s * (k : ℝ)) / p by
        rw [neg_div]
        linarith only [hdiv])
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) 1, Real.rpow_one] at h
    exact h
  -- (c) the value slot at the maximising scale
  have hgamsmall : gam ≤ 1 / (2 * C) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hCgam]
  have hvalue : 1 / (2 * C) ≤ gam * (k : ℝ) := by
    have hck : gam * (C⁻¹ * gam⁻¹ - 1) ≤ gam * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk' hgam.le
    have hid : gam * (C⁻¹ * gam⁻¹ - 1) = C⁻¹ - gam := by
      field_simp
    have hhalf : C⁻¹ - 1 / (2 * C) = 1 / (2 * C) := by
      field_simp
      ring
    linarith only [hck, hid, hhalf, hgamsmall]
  -- (d) the base comparison, with a factor two to spare for the discount
  have hkey : 6 / C < Real.sqrt (1 / (2 * C)) := by
    rw [Real.lt_sqrt (by positivity), div_pow, div_lt_div_iff₀ (by positivity)
      (by positivity)]
    have hmul : 72 * C < C * C := mul_lt_mul_of_pos_right hC hC0
    have hsq : C ^ 2 = C * C := by ring
    linarith only [hmul, hsq]
  have hsqrtlb : Real.sqrt (1 / (2 * C)) ≤ Real.sqrt (gam * (k : ℝ)) :=
    Real.sqrt_le_sqrt hvalue
  have hbase : C * Real.sqrt gam * s⁻¹ <
      2⁻¹ * ((3 : ℝ) ^ (-(s * (k : ℝ)) / p) * Real.sqrt (gam * (k : ℝ))) := by
    have hstep : 2⁻¹ * ((3 : ℝ)⁻¹ * Real.sqrt (1 / (2 * C))) ≤
        2⁻¹ * ((3 : ℝ) ^ (-(s * (k : ℝ)) / p) * Real.sqrt (gam * (k : ℝ))) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul hB hsqrtlb (Real.sqrt_nonneg _) ?_)
        (by norm_num)
      exact Real.rpow_nonneg (by norm_num) _
    have hid : 2⁻¹ * ((3 : ℝ)⁻¹ * Real.sqrt (1 / (2 * C))) =
        Real.sqrt (1 / (2 * C)) / 6 := by ring
    have hlt : C⁻¹ < Real.sqrt (1 / (2 * C)) / 6 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
      have hid2 : C⁻¹ * 6 = 6 / C := by
        field_simp
      linarith only [hkey, hid2]
    linarith only [hA, hstep, hid, hlt]
  -- (e) raise to the `p`-th power and refold
  have hLHS0 : (0 : ℝ) ≤ C * Real.sqrt gam * s⁻¹ := by positivity
  have hlt := Real.rpow_lt_rpow hLHS0 hbase hp0
  have hfold : (2⁻¹ * ((3 : ℝ) ^ (-(s * (k : ℝ)) / p) * Real.sqrt (gam * (k : ℝ)))) ^ p =
      (2 : ℝ)⁻¹ ^ p *
        ((3 : ℝ) ^ (-(s * (k : ℝ))) * (gam * (k : ℝ)) ^ (p / 2)) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hgk0 : (0 : ℝ) ≤ gam * (k : ℝ) := mul_nonneg hgam.le hk0
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (k : ℝ)) / p) := Real.rpow_nonneg (by norm_num) _
    rw [Real.mul_rpow (by norm_num) (mul_nonneg h3 (Real.sqrt_nonneg _)),
      Real.mul_rpow h3 (Real.sqrt_nonneg _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_eq_rpow, ← Real.rpow_mul hgk0]
    rw [div_mul_cancel₀ _ hp0.ne', show (1 : ℝ) / 2 * p = p / 2 from by ring]
  -- (f) the discount absorbs the factor `2^{-p}`
  have hps : 4 ≤ p * s := by
    have hsqle : Real.sqrt gam ≤ s / C ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [hs]
    have hgle : gam ≤ (s / C ^ 2) ^ 2 := by
      have h2 : Real.sqrt gam ^ 2 ≤ (s / C ^ 2) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqle 2
      have h3 : Real.sqrt gam ^ 2 = gam := Real.sq_sqrt hgam.le
      linarith only [h2, h3]
    have hC4 : gam * C ^ 4 ≤ s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hgle (by positivity : (0 : ℝ) ≤ C ^ 4)
      have hid : (s / C ^ 2) ^ 2 * C ^ 4 = s ^ 2 := by
        field_simp
      linarith only [h, hid]
    have hps' : p * s = C⁻¹ * (gam⁻¹ * s ^ 2) := by
      rw [hp]
      ring
    have hstep : C ^ 3 ≤ C⁻¹ * (gam⁻¹ * s ^ 2) := by
      have hginv : C ^ 4 ≤ gam⁻¹ * s ^ 2 := by
        rw [← le_div_iff₀' hgam, div_eq_inv_mul] at hC4
        have hid : gam⁻¹ * s ^ 2 = gam⁻¹ * s ^ 2 := rfl
        linarith only [hC4, hid]
      have h := mul_le_mul_of_nonneg_left hginv (le_of_lt (inv_pos.mpr hC0))
      have hid : C⁻¹ * C ^ 4 = C ^ 3 := by
        field_simp
      linarith only [h, hid]
    have hC3 : (4 : ℝ) ≤ C ^ 3 := by
      have h1 : (72 : ℝ) ^ 3 ≤ C ^ 3 := pow_le_pow_left₀ (by norm_num) hC.le 3
      linarith only [h1]
    linarith only [hps', hstep, hC3]
  have hdiscount : (2 : ℝ)⁻¹ ^ p ≤ 1 - (3 : ℝ) ^ (-s) := by
    have hhalf := half_le_one_sub_rpow_three_neg (u := s) hs0 hs1
    have hbern := one_add_half_le_two_rpow hp0.le
    have hpge : 4 / s ≤ p := (div_le_iff₀ hs0).mpr (by linarith only [hps])
    have h2s : 2 / s ≤ 1 + p / 2 := by
      have h4 : 2 / s ≤ p / 2 := by
        rw [div_le_div_iff₀ hs0 (by norm_num : (0 : ℝ) < 2)]
        have h := mul_le_mul_of_nonneg_left hpge hs0.le
        have hid : s * (4 / s) = 4 := by
          field_simp
        linarith only [h, hid]
      linarith only [h4]
    have h2p0 : (0 : ℝ) < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
    have hge : 2 / s ≤ (2 : ℝ) ^ p := by linarith only [h2s, hbern]
    have hinv : ((2 : ℝ) ^ p)⁻¹ ≤ s / 2 := by
      have hpos : (0 : ℝ) < 2 / s := by positivity
      have h := inv_anti₀ hpos hge
      have hid : (2 / s)⁻¹ = s / 2 := by
        field_simp
      linarith only [h, hid]
    have hrw : (2 : ℝ)⁻¹ ^ p = ((2 : ℝ) ^ p)⁻¹ := Real.inv_rpow (by norm_num) p
    linarith only [hinv, hrw, hhalf]
  have hterm0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (k : ℝ))) * (gam * (k : ℝ)) ^ (p / 2) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (mul_nonneg hgam.le hk0) _)
  have hmono : (2 : ℝ)⁻¹ ^ p *
      ((3 : ℝ) ^ (-(s * (k : ℝ))) * (gam * (k : ℝ)) ^ (p / 2)) ≤
      (1 - (3 : ℝ) ^ (-s)) *
        ((3 : ℝ) ^ (-(s * (k : ℝ))) * (gam * (k : ℝ)) ^ (p / 2)) :=
    mul_le_mul_of_nonneg_right hdiscount hterm0
  rw [hfold] at hlt
  linarith only [hlt, hmono]

end Algsuperdiff.Section4.Provider.BoundsEaL
