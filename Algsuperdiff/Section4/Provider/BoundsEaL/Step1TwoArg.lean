/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section3.Provider.ErrorComparison.InftyToQ

/-!
# Step 1: the two-argument `(∞, 2) → (p, 2)` exponent reduction

## The target

`l.bounds.mathcal.E.aL` opens with the exponent reduction

```
𝓔_{s,∞,2}(□_m, n; ã_{L,m}, σ̄_m)^p
  ≤ 3^{d(m-n)} (𝔠_{2s} / 𝔠_s)^{p/2} 𝓔_{s-d/p, p, 2}(□_m, n; ã_{L,m}, σ̄_m)^p ,
```

obtained by applying `e.mathcalE.infty.to.q` with exponents `p` and `2` and
raising to the power `p`, "using that `p ≥ 2ds^{-1}`".  Here `𝔠_r = 1 -
3^{-r}`, so `𝔠_{2s} = geometricDiscount s 2` and `𝔠_s = geometricDiscount s 1`.

Two features of the printed display are what this file supplies:

* the **truncation index is free** (`n ≤ m`), whereas the proved Section 3
  endpoint `Localization.homogenizationErrorOnCube_sq_le_breakdown` works with
  `Ch02.HomogenizationErrorOnCube`, i.e. with `n` pinned to `Q.scale`;
* the printed denominator is `𝔠_s` rather than the mechanically produced
  `𝔠_{2(s-d/p)}`.  The two agree exactly at the manuscript's own exponent
  `p = 2ds^{-1}` (there `s - d/p = s/2`, so `2(s-d/p) = s`), and for larger `p`
  the printed form is the weaker, valid one: `p ≥ 2ds^{-1}` is equivalent to
  `2d/p ≤ s`, hence `s ≤ 2(s - d/p)` and `𝔠_s ≤ 𝔠_{2(s-d/p)}`.  **This is
  exactly the role of the `p ≥ 2ds^{-1}` floor**, which also keeps the shifted
  index `s - d/p ≥ s/2` positive.

## Main results

* `homogenizationError_infinity_two_rpow_le` — the same display at `q = 2`,
  raised to the power `p`, in the mechanically produced form (denominator
  `𝔠_{2(s-d/p)}`).
* `step1_exponent_reduction` — **the printed display** (denominator `𝔠_s`),
  under the source's own floor `2ds^{-1} ≤ p`.
* `step1_exponent_reduction_originCube` — the same at the development carrier
  `□_m`, with the prefactor written as `3^{d(m-n)}` in the anchor's cast
  spelling `(m : ℝ) - (n : ℝ)`.

## References

* ABK26, `e.mathcalE.infty.to.q`, (statement and proof).
* ABK26, `d.mathcal.E`; `𝔠_r`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book
open Algsuperdiff.Section3.Provider

noncomputable section

variable {d : ℕ}

/-! ## Re-derived ingredients -/

/-- Nonnegativity of the finite-`p` one-scale response. -/
theorem scaleResponseAtScale_finite_nonneg [NeZero d] (Q : TriadicCube d) (k : ℤ)
    (p : ℝ) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ Ch02.scaleResponseAtScale Q k (.finite p) F a0 := by
  rw [ErrorComparison.scaleResponseAtScale_finite_eq]
  exact Real.rpow_nonneg
    (ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg Q k F a0 p) _

/-- The finite-`p` one-scale response obeys the same uniform deterministic bound
as the `p = ∞` one. -/
theorem scaleResponseAtScale_finite_le_uniform [NeZero d] (Q : TriadicCube d)
    {k : ℤ} (hk : k ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {p : ℝ} (hp : 0 < p) :
    Ch02.scaleResponseAtScale Q k (.finite p) F a0 ≤
      Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (1 / 2 : ℝ) := by
  have hB : 0 ≤ Ch02.normalizedBlockResponseUniformBound Q F a0 := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact le_trans (Ch02.normalizedBlockResponseMax_nonneg R F a0)
      (Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
        (a := F) (Q := Q) (R := R) (k := k) a0 hR)
  have haverage :
      Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) ≤
        Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (p / 2) := by
    refine ErrorComparison.finsetAverageReal_le _ (Real.rpow_nonneg hB _) ?_
    intro R hR
    exact Real.rpow_le_rpow (Ch02.normalizedBlockResponseMax_nonneg R F a0)
      (Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
        (a := F) (Q := Q) (R := R) (k := k) a0 hR) (by positivity)
  rw [ErrorComparison.scaleResponseAtScale_finite_eq]
  have hstep :
      Real.rpow
          (Ch02.finsetAverageReal (descendantsAtScale Q k)
            (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)))
          (1 / p) ≤
        Real.rpow
          (Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (p / 2))
          (1 / p) :=
    Real.rpow_le_rpow
      (ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg Q k F a0 p) haverage
      (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [ErrorComparison.rpow_rpow hB]
  congr 1
  field_simp

/-- The weight identity behind the printed computation: the `𝓔_{s,∞,q}` weight
times the descendant-count factor is a constant multiple of the
`𝓔_{s - d/p, p, q}` weight. -/
theorem geometricWeight_mul_rpow_three_eq {D : ℕ} {s p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) (ht : 0 < s - (D : ℝ) / p) (g l : ℕ) :
    Ch02.geometricWeight s q l *
        Real.rpow (3 : ℝ) ((D : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p)) =
      Real.rpow (3 : ℝ) ((D : ℝ) / p * q * (g : ℝ)) *
          (Ch02.geometricDiscount s q /
            Ch02.geometricDiscount (s - (D : ℝ) / p) q) *
        Ch02.geometricWeight (s - (D : ℝ) / p) q l := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hdiscount_pos : 0 < Ch02.geometricDiscount (s - (D : ℝ) / p) q :=
    Homogenization.geometricDiscount_pos (s := s - (D : ℝ) / p) (q := q)
      (mul_pos ht hq)
  have hpow1 :
      Real.rpow (3 : ℝ) (-s * q * (l : ℝ)) *
          Real.rpow (3 : ℝ) ((D : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p)) =
        Real.rpow (3 : ℝ)
          (-s * q * (l : ℝ) + (D : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p)) :=
    (Real.rpow_add h3 _ _).symm
  have hpow2 :
      Real.rpow (3 : ℝ) ((D : ℝ) / p * q * (g : ℝ)) *
          Real.rpow (3 : ℝ) (-(s - (D : ℝ) / p) * q * (l : ℝ)) =
        Real.rpow (3 : ℝ)
          ((D : ℝ) / p * q * (g : ℝ) + -(s - (D : ℝ) / p) * q * (l : ℝ)) :=
    (Real.rpow_add h3 _ _).symm
  have hexp :
      -s * q * (l : ℝ) + (D : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p) =
        (D : ℝ) / p * q * (g : ℝ) + -(s - (D : ℝ) / p) * q * (l : ℝ) := by
    field_simp
    ring
  have halg : ∀ cs c' X Y : ℝ, c' ≠ 0 → cs * (X * Y) = X * (cs / c') * (c' * Y) := by
    intro cs c' X Y hc'
    field_simp
  unfold Ch02.geometricWeight
  calc
    Ch02.geometricDiscount s q * Real.rpow (3 : ℝ) (-s * q * (l : ℝ)) *
        Real.rpow (3 : ℝ) ((D : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p)) =
        Ch02.geometricDiscount s q *
          (Real.rpow (3 : ℝ) (-s * q * (l : ℝ)) *
            Real.rpow (3 : ℝ) ((D : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p))) := by
      ring
    _ = Ch02.geometricDiscount s q *
        Real.rpow (3 : ℝ)
          ((D : ℝ) / p * q * (g : ℝ) + -(s - (D : ℝ) / p) * q * (l : ℝ)) := by
      rw [hpow1, hexp]
    _ = Ch02.geometricDiscount s q *
        (Real.rpow (3 : ℝ) ((D : ℝ) / p * q * (g : ℝ)) *
          Real.rpow (3 : ℝ) (-(s - (D : ℝ) / p) * q * (l : ℝ))) := by
      rw [hpow2]
    _ = Real.rpow (3 : ℝ) ((D : ℝ) / p * q * (g : ℝ)) *
          (Ch02.geometricDiscount s q /
            Ch02.geometricDiscount (s - (D : ℝ) / p) q) *
        (Ch02.geometricDiscount (s - (D : ℝ) / p) q *
          Real.rpow (3 : ℝ) (-(s - (D : ℝ) / p) * q * (l : ℝ))) :=
      halg _ _ _ _ (ne_of_gt hdiscount_pos)

/-! ## The two-argument display `e.mathcalE.infty.to.q` -/

/-- **`e.mathcalE.infty.to.q`** (ABK26) for finite `p` and finite `q`, at a
truncation index `n ≤ Q.scale`. -/
theorem homogenizationError_infinity_le_finite [NeZero d] (Q : TriadicCube d)
    {n : ℤ} (hn : n ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {s p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : (d : ℝ) / p < s) :
    Ch02.HomogenizationError Q n s .infinity (.finite q) F a0 ≤
      Real.rpow (3 : ℝ) ((d : ℝ) / p * ((Q.scale - n : ℤ) : ℝ)) *
          Real.rpow
            (Ch02.geometricDiscount s q /
              Ch02.geometricDiscount (s - (d : ℝ) / p) q) (1 / q) *
        Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p) (.finite q)
          F a0 := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have ht0 : 0 < s - (d : ℝ) / p := sub_pos.mpr hs
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (d : ℝ) / p) hs
  set g : ℕ := Int.toNat (Q.scale - n) with hgdef
  have hg : ((g : ℕ) : ℤ) = Q.scale - n := Int.toNat_of_nonneg (sub_nonneg.mpr hn)
  have hgR : ((g : ℕ) : ℝ) = ((Q.scale - n : ℤ) : ℝ) := by exact_mod_cast hg
  set u : ℕ → ℝ := fun l =>
    Ch02.geometricWeight s q l *
      Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity F a0) q
    with hudef
  set v : ℕ → ℝ := fun l =>
    Ch02.geometricWeight (s - (d : ℝ) / p) q l *
      Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) q
    with hvdef
  set K : ℝ :=
    Real.rpow (3 : ℝ) ((d : ℝ) / p * q * (g : ℝ)) *
      (Ch02.geometricDiscount s q /
        Ch02.geometricDiscount (s - (d : ℝ) / p) q) with hKdef
  have hdiscount_s_pos : 0 < Ch02.geometricDiscount s q :=
    Homogenization.geometricDiscount_pos (s := s) (q := q) (mul_pos hs0 hq0)
  have hdiscount_t_pos : 0 < Ch02.geometricDiscount (s - (d : ℝ) / p) q :=
    Homogenization.geometricDiscount_pos (s := s - (d : ℝ) / p) (q := q)
      (mul_pos ht0 hq0)
  have hK_nonneg : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      (div_nonneg hdiscount_s_pos.le hdiscount_t_pos.le)
  have hscale : ∀ l : ℕ, n - (l : ℤ) ≤ Q.scale := fun l =>
    (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
  have hdepth : ∀ l : ℕ, Int.toNat (Q.scale - (n - (l : ℤ))) = g + l := by
    intro l
    have hrewrite : Q.scale - (n - (l : ℤ)) = (Q.scale - n) + (l : ℤ) := by ring
    rw [hrewrite, Int.toNat_add (sub_nonneg.mpr hn) (Int.natCast_nonneg l)]
    simp only [hgdef, Int.toNat_natCast]
  have hweight_nonneg : ∀ l : ℕ, 0 ≤ Ch02.geometricWeight s q l := fun l =>
    Homogenization.geometricWeight_nonneg (s := s) (q := q) l (mul_pos hs0 hq0).le
  have hu_nonneg : ∀ l : ℕ, 0 ≤ u l := by
    intro l
    rw [hudef]
    exact mul_nonneg (hweight_nonneg l)
      (Real.rpow_nonneg
        (Ch02.scaleResponseAtScale_infinity_nonneg Q (hscale l) F a0) q)
  have hv_nonneg : ∀ l : ℕ, 0 ≤ v l := by
    intro l
    rw [hvdef]
    exact mul_nonneg
      (Homogenization.geometricWeight_nonneg (s := s - (d : ℝ) / p) (q := q) l
        (mul_pos ht0 hq0).le)
      (Real.rpow_nonneg (scaleResponseAtScale_finite_nonneg Q (n - (l : ℤ)) p F a0) q)
  have hsumv : Summable v := by
    rw [hvdef]
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s - (d : ℝ) / p) (q := q)
      (C := Real.rpow
        (Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (1 / 2 : ℝ)) q)
      (mul_pos ht0 hq0)
      (fun l => Real.rpow_nonneg
        (scaleResponseAtScale_finite_nonneg Q (n - (l : ℤ)) p F a0) q)
      (fun l => ?_)
    exact Real.rpow_le_rpow
      (scaleResponseAtScale_finite_nonneg Q (n - (l : ℤ)) p F a0)
      (scaleResponseAtScale_finite_le_uniform Q (hscale l) F a0 hp0) hq0.le
  have hterm : ∀ l : ℕ, u l ≤ K * v l := by
    intro l
    have hstep :=
      ErrorComparison.scaleResponseAtScale_infinity_rpow_le_card_mul_finite Q
        (hscale l) F a0 hp0 hq0
    have hcardEq :
        ((descendantsAtScale Q (n - (l : ℤ))).card : ℝ) =
          Real.rpow (3 : ℝ) ((d : ℝ) * ((g : ℝ) + (l : ℝ))) := by
      rw [ErrorComparison.card_descendantsAtScale_eq_rpow Q (hscale l), hdepth l]
      congr 1
      push_cast
      ring
    have hcardPow :
        Real.rpow ((descendantsAtScale Q (n - (l : ℤ))).card : ℝ) (q / p) =
          Real.rpow (3 : ℝ) ((d : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p)) := by
      rw [hcardEq, ErrorComparison.rpow_rpow (by norm_num : (0 : ℝ) ≤ 3)]
    rw [hcardPow] at hstep
    have hweights := geometricWeight_mul_rpow_three_eq (D := d) (s := s) (p := p)
      (q := q) hp0 hq0 ht0 g l
    rw [hudef, hvdef, hKdef]
    calc
      Ch02.geometricWeight s q l *
          Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity F a0) q ≤
          Ch02.geometricWeight s q l *
            (Real.rpow (3 : ℝ) ((d : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p)) *
              Real.rpow
                (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) q) :=
        mul_le_mul_of_nonneg_left hstep (hweight_nonneg l)
      _ = (Ch02.geometricWeight s q l *
            Real.rpow (3 : ℝ) ((d : ℝ) * ((g : ℝ) + (l : ℝ)) * (q / p))) *
            Real.rpow
              (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) q := by
        ring
      _ = Real.rpow (3 : ℝ) ((d : ℝ) / p * q * (g : ℝ)) *
            (Ch02.geometricDiscount s q /
              Ch02.geometricDiscount (s - (d : ℝ) / p) q) *
            (Ch02.geometricWeight (s - (d : ℝ) / p) q l *
              Real.rpow
                (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) q) := by
        rw [hweights]
        ring
  have hsumu : Summable u :=
    Summable.of_nonneg_of_le hu_nonneg hterm (hsumv.mul_left K)
  have hsumLe : (∑' l : ℕ, u l) ≤ K * ∑' l : ℕ, v l := by
    calc
      (∑' l : ℕ, u l) ≤ ∑' l : ℕ, K * v l :=
        Summable.tsum_le_tsum hterm hsumu (hsumv.mul_left K)
      _ = K * ∑' l : ℕ, v l := hsumv.tsum_mul_left K
  have hU_nonneg : 0 ≤ ∑' l : ℕ, u l := tsum_nonneg hu_nonneg
  have hV_nonneg : 0 ≤ ∑' l : ℕ, v l := tsum_nonneg hv_nonneg
  have hKrpow :
      Real.rpow K (1 / q) =
        Real.rpow (3 : ℝ) ((d : ℝ) / p * ((Q.scale - n : ℤ) : ℝ)) *
          Real.rpow
            (Ch02.geometricDiscount s q /
              Ch02.geometricDiscount (s - (d : ℝ) / p) q) (1 / q) := by
    have hfactor :
        Real.rpow (Real.rpow (3 : ℝ) ((d : ℝ) / p * q * (g : ℝ))) (1 / q) =
          Real.rpow (3 : ℝ) ((d : ℝ) / p * ((Q.scale - n : ℤ) : ℝ)) := by
      rw [ErrorComparison.rpow_rpow (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      rw [← hgR]
      field_simp
    have h3g : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) / p * q * (g : ℝ)) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    have hdiv :
        (0 : ℝ) ≤
          Ch02.geometricDiscount s q /
            Ch02.geometricDiscount (s - (d : ℝ) / p) q :=
      div_nonneg hdiscount_s_pos.le hdiscount_t_pos.le
    rw [hKdef, ErrorComparison.mul_rpow' h3g hdiv (1 / q), hfactor]
  rw [ErrorComparison.homogenizationError_finite_eq_rpow_tsum,
    ErrorComparison.homogenizationError_finite_eq_rpow_tsum, ← hudef, ← hvdef]
  calc
    Real.rpow (∑' l : ℕ, u l) (1 / q) ≤ Real.rpow (K * ∑' l : ℕ, v l) (1 / q) :=
      Real.rpow_le_rpow hU_nonneg hsumLe (by positivity)
    _ = Real.rpow K (1 / q) * Real.rpow (∑' l : ℕ, v l) (1 / q) :=
      Real.mul_rpow hK_nonneg hV_nonneg
    _ = Real.rpow (3 : ℝ) ((d : ℝ) / p * ((Q.scale - n : ℤ) : ℝ)) *
          Real.rpow
            (Ch02.geometricDiscount s q /
              Ch02.geometricDiscount (s - (d : ℝ) / p) q) (1 / q) *
        Real.rpow (∑' l : ℕ, v l) (1 / q) := by rw [hKrpow]

/-! ## Nonnegativity of the two finite-`q` errors -/

/-- Nonnegativity of the finite-`q` two-argument error, from the nonnegativity of
its one-scale responses. -/
theorem homogenizationError_finite_q_nonneg [NeZero d] (Q : TriadicCube d) (n : ℤ)
    {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (P : Ch02.MultiscaleExponent)
    (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (hresp : ∀ l : ℕ, 0 ≤ Ch02.scaleResponseAtScale Q (n - (l : ℤ)) P F a0) :
    0 ≤ Ch02.HomogenizationError Q n s P (.finite q) F a0 := by
  rw [ErrorComparison.homogenizationError_finite_eq_rpow_tsum]
  refine Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg ?_ ?_) _
  · exact Homogenization.geometricWeight_nonneg (s := s) (q := q) l (mul_pos hs hq).le
  · exact Real.rpow_nonneg (hresp l) _

/-! ## The printed Step-1 display -/

/-- `e.mathcalE.infty.to.q` at `q = 2`, raised to the power `p`: the exponent
reduction in the mechanically produced form, with denominator
`𝔠_{2(s-d/p)} = geometricDiscount (s - d/p) 2`. -/
theorem homogenizationError_infinity_two_rpow_le [NeZero d] (Q : TriadicCube d)
    {n : ℤ} (hn : n ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {s p : ℝ} (hp : 1 ≤ p) (hs : (d : ℝ) / p < s) :
    Real.rpow (Ch02.HomogenizationError Q n s .infinity (.finite 2) F a0) p ≤
      Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
          Real.rpow (Ch02.geometricDiscount s 2 /
            Ch02.geometricDiscount (s - (d : ℝ) / p) 2) (p / 2) *
        Real.rpow (Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p)
          (.finite 2) F a0) p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ht0 : 0 < s - (d : ℝ) / p := sub_pos.mpr hs
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (d : ℝ) / p) hs
  have hdiscount_s_pos : 0 < Ch02.geometricDiscount s 2 :=
    Homogenization.geometricDiscount_pos (s := s) (q := (2 : ℝ)) (by positivity)
  have hdiscount_t_pos : 0 < Ch02.geometricDiscount (s - (d : ℝ) / p) 2 :=
    Homogenization.geometricDiscount_pos (s := s - (d : ℝ) / p) (q := (2 : ℝ))
      (by positivity)
  have hdiv : (0 : ℝ) ≤ Ch02.geometricDiscount s 2 /
      Ch02.geometricDiscount (s - (d : ℝ) / p) 2 :=
    div_nonneg hdiscount_s_pos.le hdiscount_t_pos.le
  have hA0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) / p * ((Q.scale - n : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hB0 : (0 : ℝ) ≤ Real.rpow (Ch02.geometricDiscount s 2 /
      Ch02.geometricDiscount (s - (d : ℝ) / p) 2) (1 / 2 : ℝ) :=
    Real.rpow_nonneg hdiv _
  have hY0 : 0 ≤ Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p)
      (.finite 2) F a0 :=
    homogenizationError_finite_q_nonneg Q n ht0 (by norm_num) _ F a0
      (fun l => scaleResponseAtScale_finite_nonneg Q (n - (l : ℤ)) p F a0)
  have hX0 : 0 ≤ Ch02.HomogenizationError Q n s .infinity (.finite 2) F a0 :=
    homogenizationError_finite_q_nonneg Q n hs0 (by norm_num) _ F a0
      (fun l => Ch02.scaleResponseAtScale_infinity_nonneg Q
        ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn) F a0)
  have hdisp :=
    homogenizationError_infinity_le_finite Q hn F a0 hp (by norm_num : (1 : ℝ) ≤ 2) hs
  have hraise :
      Real.rpow (Ch02.HomogenizationError Q n s .infinity (.finite 2) F a0) p ≤
        Real.rpow
          (Real.rpow (3 : ℝ) ((d : ℝ) / p * ((Q.scale - n : ℤ) : ℝ)) *
              Real.rpow (Ch02.geometricDiscount s 2 /
                Ch02.geometricDiscount (s - (d : ℝ) / p) 2) (1 / 2 : ℝ) *
            Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p) (.finite 2)
              F a0) p :=
    Real.rpow_le_rpow hX0 hdisp hp0.le
  refine hraise.trans (le_of_eq ?_)
  rw [ErrorComparison.mul_rpow' (mul_nonneg hA0 hB0) hY0 p, ErrorComparison.mul_rpow' hA0 hB0 p,
    ErrorComparison.rpow_rpow (by norm_num : (0 : ℝ) ≤ 3), ErrorComparison.rpow_rpow hdiv]
  have hexpA : (d : ℝ) / p * ((Q.scale - n : ℤ) : ℝ) * p =
      (d : ℝ) * ((Q.scale - n : ℤ) : ℝ) := by
    field_simp
  have hexpB : (1 / 2 : ℝ) * p = p / 2 := by ring
  rw [hexpA, hexpB]

/-- **The printed Step-1 exponent reduction** (ABK26):

```
𝓔_{s,∞,2}(Q, n; a, a0)^p
  ≤ 3^{d(Q.scale-n)} (𝔠_{2s} / 𝔠_s)^{p/2} 𝓔_{s-d/p, p, 2}(Q, n; a, a0)^p .
```

The hypothesis `2ds^{-1} ≤ p` is the source's own floor on `p`; it is what
converts the mechanically produced denominator `𝔠_{2(s-d/p)}` into the printed
`𝔠_s` (and, en route, keeps `s - d/p ≥ s/2 > 0`).  `s ≤ 1` is used only to
see `1 ≤ p` from that floor. -/
theorem step1_exponent_reduction [NeZero d] (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s p : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    Real.rpow (Ch02.HomogenizationError Q n s .infinity (.finite 2) F a0) p ≤
      Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
          Real.rpow (Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1)
            (p / 2) *
        Real.rpow (Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p)
          (.finite 2) F a0) p := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hsinv : (1 : ℝ) ≤ s⁻¹ := by
    rw [le_inv_comm₀ zero_lt_one hs, inv_one]
    exact hs1
  have hd2 : (2 : ℝ) ≤ 2 * (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hd1 (by norm_num : (0 : ℝ) ≤ 2)
    rw [mul_one] at h
    exact h
  have h2 : (2 : ℝ) ≤ 2 * (d : ℝ) * s⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hsinv
      (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
    rw [mul_one] at h
    exact hd2.trans h
  have hp1 : (1 : ℝ) ≤ p := le_trans (by norm_num) (le_trans h2 hp)
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have h2dp : 2 * (d : ℝ) / p ≤ s := by
    rw [mul_inv_le_iff₀ hs] at hp
    rw [div_le_iff₀ hp0, mul_comm s p]
    exact hp
  have hdp : (d : ℝ) / p < s := by
    have hhalf : (d : ℝ) / p < 2 * (d : ℝ) / p := by
      rw [div_lt_div_iff_of_pos_right hp0]
      have h := mul_lt_mul_of_pos_right (by norm_num : (1 : ℝ) < 2) hd0
      rw [one_mul] at h
      exact h
    exact lt_of_lt_of_le hhalf h2dp
  have ht0 : 0 < s - (d : ℝ) / p := sub_pos.mpr hdp
  have hdiscount_s_pos : 0 < Ch02.geometricDiscount s 2 :=
    Homogenization.geometricDiscount_pos (s := s) (q := (2 : ℝ)) (by positivity)
  have hdiscount_one_pos : 0 < Ch02.geometricDiscount s 1 :=
    Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ)) (by positivity)
  have hdiscount_t_pos : 0 < Ch02.geometricDiscount (s - (d : ℝ) / p) 2 :=
    Homogenization.geometricDiscount_pos (s := s - (d : ℝ) / p) (q := (2 : ℝ))
      (by positivity)
  have hexp : -(s - (d : ℝ) / p) * 2 ≤ -s * 1 := by
    have h2d : 2 * ((d : ℝ) / p) ≤ s := by
      rw [mul_div_assoc] at h2dp
      exact h2dp
    linarith only [h2d]
  have hmono : Ch02.geometricDiscount s 1 ≤
      Ch02.geometricDiscount (s - (d : ℝ) / p) 2 := by
    unfold Ch02.geometricDiscount
    exact sub_le_sub_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp) 1
  have hratio : Ch02.geometricDiscount s 2 /
        Ch02.geometricDiscount (s - (d : ℝ) / p) 2 ≤
      Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1 := by
    gcongr
  have hY0 : 0 ≤ Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p)
      (.finite 2) F a0 :=
    homogenizationError_finite_q_nonneg Q n ht0 (by norm_num) _ F a0
      (fun l => scaleResponseAtScale_finite_nonneg Q (n - (l : ℤ)) p F a0)
  have hA0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow : Real.rpow (Ch02.geometricDiscount s 2 /
        Ch02.geometricDiscount (s - (d : ℝ) / p) 2) (p / 2) ≤
      Real.rpow (Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1)
        (p / 2) :=
    Real.rpow_le_rpow (div_nonneg hdiscount_s_pos.le hdiscount_t_pos.le) hratio
      (by positivity)
  refine (homogenizationError_infinity_two_rpow_le Q hn F a0 hp1 hdp).trans ?_
  have hstep : Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
        Real.rpow (Ch02.geometricDiscount s 2 /
          Ch02.geometricDiscount (s - (d : ℝ) / p) 2) (p / 2) ≤
      Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
        Real.rpow (Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1)
          (p / 2) :=
    mul_le_mul_of_nonneg_left hpow hA0
  exact mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hY0 p)

/-- The printed Step-1 exponent reduction at the development carrier `□_m`, with
the prefactor in the anchor's cast spelling `3^{d((m : ℝ) - (n : ℝ))}`. -/
theorem step1_exponent_reduction_originCube [NeZero d] {m n : ℤ} (hnm : n ≤ m)
    (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s p : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (hp : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    Real.rpow
        (Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2) F a0)
        p ≤
      Real.rpow (3 : ℝ) ((d : ℝ) * ((m : ℝ) - (n : ℝ))) *
          Real.rpow (Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1)
            (p / 2) *
        Real.rpow (Ch02.HomogenizationError (originCube d m) n (s - (d : ℝ) / p)
          (.finite p) (.finite 2) F a0) p := by
  have hcast : (((originCube d m).scale - n : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    show ((m - n : ℤ) : ℝ) = (m : ℝ) - (n : ℝ)
    push_cast
    ring
  have hmain := step1_exponent_reduction (originCube d m) (n := n) hnm F a0 hs hs1 hp
  rw [hcast] at hmain
  exact hmain

end

end Algsuperdiff.Section4.Provider.BoundsEaL
