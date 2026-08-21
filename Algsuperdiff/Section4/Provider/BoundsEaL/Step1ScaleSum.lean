/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.Step1TwoArg

/-!
# The second printed Step-1 inequality: the scale-sum endpoint

Nothing here imports that file, and nothing here claims the anchor.

## The target

Step 1 of the proof of `l.bounds.mathcal.E.aL` chains two inequalities.  The
first one is proved in `Step1TwoArg.lean` as
`step1_exponent_reduction_originCube`; this file supplies the **second** one,

```
𝓔_{s,∞,2}(□_m, n; ã, σ̄)^p
  ≤ C^p 3^{d(m-n)} 𝔠_s ∑_{j ≤ n} 3^{-s(n-j)}
      ⨍_{z ∈ 3^j ℤ^d ∩ □_m} max_{|e|=1} J(z + □_j, ...)^{p/2} ,
```

with `C = 2` **explicitly** (see the deviation note below).  In the Lean
carrier the printed inner object

```
⨍_{z ∈ 3^j ℤ^d ∩ □_m} max_{|e|=1} J(z + □_j, A₀^{-1/2} e, A₀^{1/2} e; a)^{p/2}
```

is literally `Ch02.finsetAverageReal (descendantsAtScale □_m j) (fun R =>
Real.rpow (Ch02.normalizedBlockResponseMax R a a₀) (p/2))`: the descendants of
`□_m` at scale `j` are exactly the cubes `z + □_j` with `z ∈ 3^j ℤ^d ∩ □_m`,
and `Ch02.normalizedBlockResponseMax` is the printed `max_{|e|=1} J(·,
A₀^{-1/2} e, A₀^{1/2} e; a)` of `d.mathcal.E`.  The scale index is `j = n - l`
with `l : ℕ`, so `3^{-s(n-j)} = 3^{-s l}` and the printed sum `∑_{j = -∞}^{n}`
is the `tsum` over `l : ℕ`.

## The printed primal/adjoint split is NOT performed

The printed right side of the second inequality is a **sum of two** scale sums,
one at `ã_{L,m}` and one at `ã_{L,m}^t`, quoted "as in `e.mathcal.E.breakdown`".
That split refines the *doubled* response `𝐉(·, 𝐀₀^{-1/2} e, 𝐀₀^{1/2} e; a)` of
`d.mathcal.E` into a primal and an adjoint contribution.  The carrier here keeps
the doubled response undivided (`Ch02.normalizedBlockResponseMax`, the object
`d.mathcal.E` is defined with), so the endpoint below is the **single-term**
form: no split is claimed, and no constant is spent on one.

## Main results

* `rpow_tsum_weight_mul_le_tsum_weight_mul_rpow` — Jensen for unit-mass weights
  on `ℕ` at a real exponent `r ≥ 1` (the tangent-line proof).
* `finsetAverage_rpow_normalizedBlockResponseMax_le_uniform` — the deterministic
  uniform bound on the printed inner average.
* `homogenizationError_finite_two_rpow_le_tsum_weight_mul_average` — the Jensen
  step at the carrier: `𝓔_{t,p,2}(Q, n)^p ≤ ∑' l, w_l · (inner average)`.
* `tsum_geometricWeight_two_mul_average_le` — the weight conversion
  `𝔠_{2t} 3^{-2tl} ↦ 2 𝔠_s 3^{-sl}`.
* `step1_scaleSum_endpoint` — **the printed Step-1 endpoint** at a general cube.
* `step1_scaleSum_endpoint_originCube` — the same at the development carrier
  `□_m`, in the anchor's cast spelling `3^{d((m : ℝ) - (n : ℝ))}`.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (Step 1; the second printed inequality).
* ABK26, `d.mathcal.E`, (the inner average and the weights); `𝔠_r = 1 -
  3^{-r}`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book
open Algsuperdiff.Section3.Provider

noncomputable section

variable {d : ℕ}

/-! ## Jensen for unit-mass weights on `ℕ` -/

/-- **Jensen's inequality for unit-mass weights on `ℕ`** at a real exponent
`r ≥ 1`:

```
(∑' l, w l * f l) ^ r ≤ ∑' l, w l * (f l) ^ r ,
```

for nonnegative `w`, `f` with `∑' l, w l = 1`.

The proof is the tangent line of `x ↦ x^r` at the point `S = ∑' l, w l * f l`:
Bernoulli's inequality `1 + r t ≤ (1 + t)^r` at `t = f l / S - 1 ≥ -1` gives
`S^r + r S^{r-1} (f l - S) ≤ (f l)^r` pointwise, and the weighted sum of the
left side is exactly `S^r` because the weights have unit mass. -/
theorem rpow_tsum_weight_mul_le_tsum_weight_mul_rpow {w f : ℕ → ℝ} {r : ℝ}
    (hw : ∀ l : ℕ, 0 ≤ w l) (hf : ∀ l : ℕ, 0 ≤ f l)
    (hone : ∑' l : ℕ, w l = 1) (hsumw : Summable w)
    (hsum : Summable fun l : ℕ => w l * f l)
    (hsumr : Summable fun l : ℕ => w l * Real.rpow (f l) r) (hr : 1 ≤ r) :
    Real.rpow (∑' l : ℕ, w l * f l) r ≤ ∑' l : ℕ, w l * Real.rpow (f l) r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hS0 : 0 ≤ ∑' l : ℕ, w l * f l :=
    tsum_nonneg fun l => mul_nonneg (hw l) (hf l)
  have hRHS0 : 0 ≤ ∑' l : ℕ, w l * Real.rpow (f l) r :=
    tsum_nonneg fun l => mul_nonneg (hw l) (Real.rpow_nonneg (hf l) r)
  set S : ℝ := ∑' l : ℕ, w l * f l with hSdef
  rcases eq_or_lt_of_le hS0 with hS | hSpos
  · have hzero : Real.rpow (0 : ℝ) r = 0 := Real.zero_rpow (ne_of_gt hr0)
    rw [← hS, hzero]
    exact hRHS0
  · set A : ℝ := Real.rpow S r with hAdef
    have hA0 : 0 < A := Real.rpow_pos_of_pos hSpos r
    set alpha : ℝ := A * (1 - r) with halphadef
    set beta : ℝ := A * r / S with hbetadef
    have hterm : ∀ l : ℕ,
        alpha * w l + beta * (w l * f l) ≤ w l * Real.rpow (f l) r := by
      intro l
      have hquot : 0 ≤ f l / S := div_nonneg (hf l) hSpos.le
      have hber : 1 + r * (f l / S - 1) ≤ Real.rpow (1 + (f l / S - 1)) r :=
        one_add_mul_self_le_rpow_one_add (by linarith only [hquot]) hr
      have hsimp : (1 : ℝ) + (f l / S - 1) = f l / S := by ring
      rw [hsimp] at hber
      have hmulA : A * (1 + r * (f l / S - 1)) ≤ A * Real.rpow (f l / S) r :=
        mul_le_mul_of_nonneg_left hber hA0.le
      have hcancel : Real.rpow (f l / S) r * Real.rpow S r = Real.rpow (f l) r := by
        have hsplit : Real.rpow (f l / S * S) r =
            Real.rpow (f l / S) r * Real.rpow S r := Real.mul_rpow hquot hSpos.le
        have hfs : f l / S * S = f l := by
          field_simp
        rw [hfs] at hsplit
        exact hsplit.symm
      have hAright : A * Real.rpow (f l / S) r = Real.rpow (f l) r := by
        rw [hAdef, mul_comm]
        exact hcancel
      have hleft : alpha + beta * f l = A * (1 + r * (f l / S - 1)) := by
        rw [halphadef, hbetadef]
        field_simp
        ring
      have hkey : alpha + beta * f l ≤ Real.rpow (f l) r := by
        rw [hleft, ← hAright]
        exact hmulA
      have hmul := mul_le_mul_of_nonneg_left hkey (hw l)
      calc
        alpha * w l + beta * (w l * f l) = w l * (alpha + beta * f l) := by ring
        _ ≤ w l * Real.rpow (f l) r := hmul
    have hsumcomb : Summable fun l : ℕ => alpha * w l + beta * (w l * f l) :=
      (hsumw.mul_left alpha).add (hsum.mul_left beta)
    have hle : (∑' l : ℕ, (alpha * w l + beta * (w l * f l))) ≤
        ∑' l : ℕ, w l * Real.rpow (f l) r :=
      Summable.tsum_le_tsum hterm hsumcomb hsumr
    have hval : (∑' l : ℕ, (alpha * w l + beta * (w l * f l))) = A := by
      rw [Summable.tsum_add (hsumw.mul_left alpha) (hsum.mul_left beta),
        hsumw.tsum_mul_left, hsum.tsum_mul_left, hone, ← hSdef, halphadef, hbetadef]
      field_simp
      ring
    linarith only [hle, hval]

/-! ## The geometric discount and weight bookkeeping -/

/-- `𝔠_{2s} = 𝔠_s (1 + 3^{-s})`, from `1 - x^2 = (1-x)(1+x)` at `x = 3^{-s}`. -/
theorem geometricDiscount_two_eq_one_mul (s : ℝ) :
    Ch02.geometricDiscount s 2 =
      Ch02.geometricDiscount s 1 * (1 + Real.rpow (3 : ℝ) (-s * 1)) := by
  have hx : Real.rpow (3 : ℝ) (-s * 2) =
      Real.rpow (3 : ℝ) (-s * 1) * Real.rpow (3 : ℝ) (-s * 1) := by
    have hadd : Real.rpow (3 : ℝ) (-s * 1 + -s * 1) =
        Real.rpow (3 : ℝ) (-s * 1) * Real.rpow (3 : ℝ) (-s * 1) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
    have hexp : -s * 2 = -s * 1 + -s * 1 := by ring
    rw [hexp]
    exact hadd
  unfold Ch02.geometricDiscount
  rw [hx]
  ring

/-- `3^{-s} ≤ 1` for `0 ≤ s`. -/
theorem rpow_three_neg_le_one {s : ℝ} (hs : 0 ≤ s) :
    Real.rpow (3 : ℝ) (-s * 1) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith only [hs])

/-- The printed ratio of discounts is at most `2`: `𝔠_{2s} / 𝔠_s = 1 + 3^{-s}`. -/
theorem geometricDiscount_two_div_one_le_two {s : ℝ} (hs : 0 < s) :
    Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1 ≤ 2 := by
  have hcs : 0 < Ch02.geometricDiscount s 1 :=
    Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ)) (by linarith only [hs])
  have hne : Ch02.geometricDiscount s 1 ≠ 0 := ne_of_gt hcs
  have hx : Real.rpow (3 : ℝ) (-s * 1) ≤ 1 := rpow_three_neg_le_one hs.le
  have hcancel : Ch02.geometricDiscount s 1 * (1 + Real.rpow (3 : ℝ) (-s * 1)) /
      Ch02.geometricDiscount s 1 = 1 + Real.rpow (3 : ℝ) (-s * 1) := by
    field_simp
  rw [geometricDiscount_two_eq_one_mul s, hcancel]
  linarith only [hx]

/-- `𝔠_{2t} ≤ 2 𝔠_s` whenever `t ≤ s`. -/
theorem geometricDiscount_two_le_two_mul_one {s t : ℝ} (hs : 0 < s) (hts : t ≤ s) :
    Ch02.geometricDiscount t 2 ≤ 2 * Ch02.geometricDiscount s 1 := by
  have hcs : 0 < Ch02.geometricDiscount s 1 :=
    Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ)) (by linarith only [hs])
  have hmono : Ch02.geometricDiscount t 2 ≤ Ch02.geometricDiscount s 2 := by
    unfold Ch02.geometricDiscount
    have hpow : Real.rpow (3 : ℝ) (-s * 2) ≤ Real.rpow (3 : ℝ) (-t * 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith only [hts])
    linarith only [hpow]
  have hx : Real.rpow (3 : ℝ) (-s * 1) ≤ 1 := rpow_three_neg_le_one hs.le
  have hfac : Ch02.geometricDiscount s 2 ≤ 2 * Ch02.geometricDiscount s 1 := by
    rw [geometricDiscount_two_eq_one_mul s]
    have hstep : Ch02.geometricDiscount s 1 * (1 + Real.rpow (3 : ℝ) (-s * 1)) ≤
        Ch02.geometricDiscount s 1 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith only [hx]) hcs.le
    linarith only [hstep]
  exact hmono.trans hfac

/-- The printed weight of `𝓔_{s,·,1}` in explicit form: `w_l = 𝔠_s 3^{-s l}`. -/
theorem geometricWeight_one_eq (s : ℝ) (l : ℕ) :
    Ch02.geometricWeight s 1 l =
      Ch02.geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * (l : ℝ)) := by
  have hexp : -s * 1 * (l : ℝ) = -s * (l : ℝ) := by ring
  unfold Ch02.geometricWeight
  rw [hexp]

/-- The weight conversion of Step 1: at `t ≤ s ≤ 2t` the `𝓔_{t,·,2}` weight is
dominated by twice the printed `𝓔_{s,·,1}` weight. -/
theorem geometricWeight_two_le_two_mul_geometricWeight_one {s t : ℝ} (hs : 0 < s)
    (hts : t ≤ s) (hst : s ≤ 2 * t) (l : ℕ) :
    Ch02.geometricWeight t 2 l ≤ 2 * Ch02.geometricWeight s 1 l := by
  have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hcs : 0 < Ch02.geometricDiscount s 1 :=
    Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ)) (by linarith only [hs])
  have hdisc : Ch02.geometricDiscount t 2 ≤ 2 * Ch02.geometricDiscount s 1 :=
    geometricDiscount_two_le_two_mul_one hs hts
  have hprod : s * (l : ℝ) ≤ 2 * t * (l : ℝ) := mul_le_mul_of_nonneg_right hst hl
  have hpow : Real.rpow (3 : ℝ) (-t * 2 * (l : ℝ)) ≤
      Real.rpow (3 : ℝ) (-s * (l : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith only [hprod])
  have hpow0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-t * 2 * (l : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hdisc0 : (0 : ℝ) ≤ Ch02.geometricDiscount t 2 := by
    have := hpow0
    unfold Ch02.geometricDiscount
    have hle : Real.rpow (3 : ℝ) (-t * 2) ≤ 1 := by
      rcases le_or_gt t 0 with ht | ht
      · exact le_trans (Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) (by linarith only [ht, hs, hst] : -t * 2 ≤ 0))
          (le_of_eq (Real.rpow_zero 3))
      · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3)
          (by linarith only [ht])
    linarith only [hle]
  have hstep : Ch02.geometricDiscount t 2 * Real.rpow (3 : ℝ) (-t * 2 * (l : ℝ)) ≤
      (2 * Ch02.geometricDiscount s 1) * Real.rpow (3 : ℝ) (-s * (l : ℝ)) :=
    mul_le_mul hdisc hpow hpow0 (by linarith only [hcs])
  rw [geometricWeight_one_eq s l]
  unfold Ch02.geometricWeight
  calc
    Ch02.geometricDiscount t 2 * Real.rpow (3 : ℝ) (-t * 2 * (l : ℝ)) ≤
        (2 * Ch02.geometricDiscount s 1) * Real.rpow (3 : ℝ) (-s * (l : ℝ)) := hstep
    _ = 2 * (Ch02.geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * (l : ℝ))) := by ring

/-! ## The deterministic uniform bound on the printed inner average -/

/-- The printed inner average `⨍_z max_{|e|=1} J(z + □_j, ·)^{p/2}` is bounded by
the one-cube uniform response bound raised to `p/2`. -/
theorem finsetAverage_rpow_normalizedBlockResponseMax_le_uniform [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) {p : ℝ} (hp : 0 ≤ p) :
    Ch02.finsetAverageReal (descendantsAtScale Q k)
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) ≤
      Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (p / 2) := by
  have hB : 0 ≤ Ch02.normalizedBlockResponseUniformBound Q F a0 := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact le_trans (Ch02.normalizedBlockResponseMax_nonneg R F a0)
      (Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
        (a := F) (Q := Q) (R := R) (k := k) a0 hR)
  refine ErrorComparison.finsetAverageReal_le _ (Real.rpow_nonneg hB _) ?_
  intro R hR
  exact Real.rpow_le_rpow (Ch02.normalizedBlockResponseMax_nonneg R F a0)
    (Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
      (a := F) (Q := Q) (R := R) (k := k) a0 hR) (by linarith only [hp])

/-! ## The Jensen step at the carrier -/

/-- **The Jensen step of Step 1.**  For `p ≥ 2` and `t > 0`,

```
𝓔_{t,p,2}(Q, n; a, a₀)^p ≤ ∑' l, 𝔠_{2t} 3^{-2tl} ⨍_z max_{|e|=1} J(z + □_{n-l}, ·)^{p/2} ,
```

i.e. the outer `p/2`-power of `d.mathcal.E`'s finite-`(p, 2)` branch is moved
inside the unit-mass geometric weights. -/
theorem homogenizationError_finite_two_rpow_le_tsum_weight_mul_average [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) {t p : ℝ} (ht : 0 < t) (hp : 2 ≤ p) :
    Real.rpow (Ch02.HomogenizationError Q n t (.finite p) (.finite 2) F a0) p ≤
      ∑' l : ℕ, Ch02.geometricWeight t 2 l *
        Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
  have hp0 : (0 : ℝ) < p := by linarith only [hp]
  have hr : (1 : ℝ) ≤ p / 2 := by linarith only [hp]
  have ht2 : (0 : ℝ) < t * 2 := by linarith only [ht]
  have hscale : ∀ l : ℕ, n - (l : ℤ) ≤ Q.scale := fun l =>
    (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
  have hX0 : ∀ l : ℕ,
      0 ≤ Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0 := fun l =>
    scaleResponseAtScale_finite_nonneg Q (n - (l : ℤ)) p F a0
  have hA0 : ∀ l : ℕ,
      0 ≤ Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    fun l => ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg Q
      (n - (l : ℤ)) F a0 p
  have hf0 : ∀ l : ℕ,
      0 ≤ Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) 2 :=
    fun l => Real.rpow_nonneg (hX0 l) 2
  have hfA : ∀ l : ℕ,
      Real.rpow
          (Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) 2)
          (p / 2) =
        Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
    intro l
    rw [ErrorComparison.rpow_rpow (hX0 l),
      ErrorComparison.scaleResponseAtScale_finite_eq Q (n - (l : ℤ)) p F a0,
      ErrorComparison.rpow_rpow (hA0 l)]
    have hexp : 1 / p * (2 * (p / 2)) = 1 := by
      field_simp
    rw [hexp]
    exact Real.rpow_one _
  have hW0 : ∀ l : ℕ, 0 ≤ Ch02.geometricWeight t 2 l := fun l =>
    Homogenization.geometricWeight_nonneg (s := t) (q := (2 : ℝ)) l ht2.le
  have hone : ∑' l : ℕ, Ch02.geometricWeight t 2 l = 1 :=
    Homogenization.tsum_geometricWeight_eq_one (s := t) (q := (2 : ℝ)) ht2
  have hsumW : Summable fun l : ℕ => Ch02.geometricWeight t 2 l :=
    Homogenization.summable_geometricWeight (s := t) (q := (2 : ℝ)) ht2
  have hsumWf : Summable fun l : ℕ => Ch02.geometricWeight t 2 l *
      Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) 2 := by
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := t) (q := (2 : ℝ))
      (C := Real.rpow
        (Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (1 / 2 : ℝ)) 2)
      ht2 hf0 (fun l => ?_)
    exact Real.rpow_le_rpow (hX0 l)
      (scaleResponseAtScale_finite_le_uniform Q (hscale l) F a0 hp0) (by norm_num)
  have hsumWA : Summable fun l : ℕ => Ch02.geometricWeight t 2 l *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := t) (q := (2 : ℝ))
      (C := Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (p / 2))
      ht2 hA0 (fun l => ?_)
    exact finsetAverage_rpow_normalizedBlockResponseMax_le_uniform Q (hscale l) F a0
      hp0.le
  have hsumWr : Summable fun l : ℕ => Ch02.geometricWeight t 2 l *
      Real.rpow
        (Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) 2)
        (p / 2) := hsumWA.congr fun l => by rw [hfA l]
  have hjensen := rpow_tsum_weight_mul_le_tsum_weight_mul_rpow hW0 hf0 hone hsumW
    hsumWf hsumWr hr
  have hRHSeq : (∑' l : ℕ, Ch02.geometricWeight t 2 l *
      Real.rpow
        (Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) 2)
        (p / 2)) =
      ∑' l : ℕ, Ch02.geometricWeight t 2 l *
        Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    tsum_congr fun l => by rw [hfA l]
  have hT0 : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight t 2 l *
      Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) (.finite p) F a0) 2 :=
    tsum_nonneg fun l => mul_nonneg (hW0 l) (hf0 l)
  rw [ErrorComparison.homogenizationError_finite_eq_rpow_tsum,
    ErrorComparison.rpow_rpow hT0, ← hRHSeq]
  have hexp : 1 / (2 : ℝ) * p = p / 2 := by ring
  rw [hexp]
  exact hjensen

/-! ## The weight conversion on the scale sum -/

/-- The scale sum at the shifted index `t ∈ [s/2, s]` is dominated by twice the
printed scale sum at `s`, with the printed discount `𝔠_s` factored out. -/
theorem tsum_geometricWeight_two_mul_average_le [NeZero d] (Q : TriadicCube d)
    {n : ℤ} (hn : n ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {s t p : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ s) (hst : s ≤ 2 * t)
    (hp : 0 ≤ p) :
    (∑' l : ℕ, Ch02.geometricWeight t 2 l *
        Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) ≤
      2 * (Ch02.geometricDiscount s 1 *
        ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
          Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
            (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) := by
  have ht2 : (0 : ℝ) < t * 2 := by linarith only [ht]
  have hs1 : (0 : ℝ) < s * 1 := by linarith only [hs]
  have hcs : 0 < Ch02.geometricDiscount s 1 :=
    Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ)) hs1
  have hscale : ∀ l : ℕ, n - (l : ℤ) ≤ Q.scale := fun l =>
    (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
  have hA0 : ∀ l : ℕ,
      0 ≤ Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    fun l => ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg Q
      (n - (l : ℤ)) F a0 p
  have hAbound : ∀ l : ℕ,
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) ≤
        Real.rpow (Ch02.normalizedBlockResponseUniformBound Q F a0) (p / 2) :=
    fun l => finsetAverage_rpow_normalizedBlockResponseMax_le_uniform Q (hscale l) F a0
      hp
  have hsumt : Summable fun l : ℕ => Ch02.geometricWeight t 2 l *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le (s := t) (q := (2 : ℝ))
      ht2 hA0 hAbound
  have hsums : Summable fun l : ℕ => Ch02.geometricWeight s 1 l *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le (s := s) (q := (1 : ℝ))
      hs1 hA0 hAbound
  have hpointwise : ∀ l : ℕ, Ch02.geometricWeight s 1 l *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) =
      Ch02.geometricDiscount s 1 * (Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
        Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) := by
    intro l
    rw [geometricWeight_one_eq s l]
    ring
  have hsumbase : Summable fun l : ℕ => Ch02.geometricDiscount s 1 *
      (Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
        Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) :=
    hsums.congr hpointwise
  have hsumplain : Summable fun l : ℕ => Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
    refine (hsumbase.mul_left (Ch02.geometricDiscount s 1)⁻¹).congr fun l => ?_
    field_simp
  have hsplit : (∑' l : ℕ, Ch02.geometricWeight s 1 l *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) =
      Ch02.geometricDiscount s 1 *
        ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
          Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
            (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
    rw [tsum_congr hpointwise]
    exact hsumplain.tsum_mul_left (Ch02.geometricDiscount s 1)
  have hterm : ∀ l : ℕ, Ch02.geometricWeight t 2 l *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) ≤
      2 * (Ch02.geometricWeight s 1 l *
        Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
          (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) := by
    intro l
    have hw := geometricWeight_two_le_two_mul_geometricWeight_one hs hts hst l
    calc
      Ch02.geometricWeight t 2 l *
          Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
            (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) ≤
          (2 * Ch02.geometricWeight s 1 l) *
            Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
              (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
        mul_le_mul_of_nonneg_right hw (hA0 l)
      _ = 2 * (Ch02.geometricWeight s 1 l *
            Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
              (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) := by
        ring
  have hle := Summable.tsum_le_tsum hterm hsumt (hsums.mul_left 2)
  rw [hsums.tsum_mul_left 2, hsplit] at hle
  exact hle

/-! ## The printed Step-1 endpoint -/

/-- **The printed Step-1 endpoint** (ABK26), single-term form, with the explicit
constant `C = 2`:

```
𝓔_{s,∞,2}(Q, n; a, a₀)^p
  ≤ 2^p 3^{d(Q.scale - n)} 𝔠_s ∑_{l ≥ 0} 3^{-s l}
      ⨍_{R ∈ descendants(Q, n - l)} max_{|e|=1} J(R, A₀^{-1/2} e, A₀^{1/2} e; a)^{p/2} .
```

The hypotheses are the source's own: `s > 0`, `s ≤ 1` and the floor
`p ≥ 2ds^{-1}`.  The floor does all three jobs: it gives `p ≥ 2` (so Jensen at
`p/2` applies and `2^{p/2} · 2 ≤ 2^p`), it gives `2(s - d/p) ≥ s` (so the
shifted weights dominate the printed ones), and it is what converts the first
inequality's `𝔠_{2s}/𝔠_s` into a constant. -/
theorem step1_scaleSum_endpoint [NeZero d] (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s p : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    Real.rpow (Ch02.HomogenizationError Q n s .infinity (.finite 2) F a0) p ≤
      Real.rpow (2 : ℝ) p * Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
        Ch02.geometricDiscount s 1 *
          ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
              (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
  -- the arithmetic of the source's floor `p ≥ 2ds^{-1}`
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
    have h := mul_le_mul_of_nonneg_left hsinv (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
    rw [mul_one] at h
    exact hd2.trans h
  have hp2 : (2 : ℝ) ≤ p := h2.trans hp
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
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
  have hts : s - (d : ℝ) / p ≤ s := by
    have hdiv : (0 : ℝ) ≤ (d : ℝ) / p := by positivity
    linarith only [hdiv]
  have hst : s ≤ 2 * (s - (d : ℝ) / p) := by
    have hdouble : 2 * ((d : ℝ) / p) ≤ s := by
      rw [mul_div_assoc] at h2dp
      exact h2dp
    linarith only [hdouble]
  -- the three inequalities of the chain
  have hstep1 := step1_exponent_reduction Q hn F a0 hs hs1 hp
  have hjensen := homogenizationError_finite_two_rpow_le_tsum_weight_mul_average Q hn F a0
    ht0 hp2
  have hweights := tsum_geometricWeight_two_mul_average_le Q hn F a0 hs ht0 hts hst hp0.le
  have hratio : Real.rpow (Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1)
      (p / 2) ≤ Real.rpow (2 : ℝ) (p / 2) := by
    have hcs : 0 < Ch02.geometricDiscount s 1 :=
      Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ)) (by linarith only [hs])
    have hc2 : 0 < Ch02.geometricDiscount s 2 :=
      Homogenization.geometricDiscount_pos (s := s) (q := (2 : ℝ)) (by linarith only [hs])
    exact Real.rpow_le_rpow (div_nonneg hc2.le hcs.le)
      (geometricDiscount_two_div_one_le_two hs) (by linarith only [hp2])
  have hcoef : Real.rpow (2 : ℝ) (p / 2) * 2 ≤ Real.rpow (2 : ℝ) p := by
    have hone : Real.rpow (2 : ℝ) 1 = 2 := Real.rpow_one 2
    have hadd : Real.rpow (2 : ℝ) (p / 2 + 1) =
        Real.rpow (2 : ℝ) (p / 2) * Real.rpow (2 : ℝ) 1 :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
    have hle : Real.rpow (2 : ℝ) (p / 2 + 1) ≤ Real.rpow (2 : ℝ) p :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith only [hp2])
    rw [hone] at hadd
    rw [← hadd]
    exact hle
  -- nonnegativity bookkeeping
  have hcs0 : (0 : ℝ) ≤ Ch02.geometricDiscount s 1 :=
    (Homogenization.geometricDiscount_pos (s := s) (q := (1 : ℝ))
      (by linarith only [hs])).le
  have hA30 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hZ0 : 0 ≤ ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
      Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
        (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
    tsum_nonneg fun l => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (ErrorComparison.finsetAverage_normalizedBlockResponseMax_rpow_nonneg Q
        (n - (l : ℤ)) F a0 p)
  have hY0 : 0 ≤ Real.rpow (Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p)
      (.finite 2) F a0) p :=
    Real.rpow_nonneg (homogenizationError_finite_q_nonneg Q n ht0 (by norm_num) _ F a0
      (fun l => scaleResponseAtScale_finite_nonneg Q (n - (l : ℤ)) p F a0)) p
  have hb0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
      Real.rpow (2 : ℝ) (p / 2) :=
    mul_nonneg hA30 (Real.rpow_nonneg (by norm_num) _)
  have hnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
      (Ch02.geometricDiscount s 1 *
        ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
          Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
            (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2))) :=
    mul_nonneg hA30 (mul_nonneg hcs0 hZ0)
  calc
    Real.rpow (Ch02.HomogenizationError Q n s .infinity (.finite 2) F a0) p ≤
        Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
            Real.rpow (Ch02.geometricDiscount s 2 / Ch02.geometricDiscount s 1)
              (p / 2) *
          Real.rpow (Ch02.HomogenizationError Q n (s - (d : ℝ) / p) (.finite p)
            (.finite 2) F a0) p := hstep1
    _ ≤ Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
            Real.rpow (2 : ℝ) (p / 2) *
          (2 * (Ch02.geometricDiscount s 1 *
            ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
              Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
                (fun R =>
                  Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hratio hA30) (hjensen.trans hweights) hY0 hb0
    _ = Real.rpow (2 : ℝ) (p / 2) * 2 *
          (Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
            (Ch02.geometricDiscount s 1 *
              ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
                Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
                  (fun R =>
                    Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)))) := by
      ring
    _ ≤ Real.rpow (2 : ℝ) p *
          (Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
            (Ch02.geometricDiscount s 1 *
              ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
                Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
                  (fun R =>
                    Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)))) :=
      mul_le_mul_of_nonneg_right hcoef hnn
    _ = Real.rpow (2 : ℝ) p *
          Real.rpow (3 : ℝ) ((d : ℝ) * ((Q.scale - n : ℤ) : ℝ)) *
          Ch02.geometricDiscount s 1 *
          ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            Ch02.finsetAverageReal (descendantsAtScale Q (n - (l : ℤ)))
              (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
      ring

/-- The printed Step-1 endpoint at the development carrier `□_m`, with the volume
prefactor in the anchor's cast spelling `3^{d((m : ℝ) - (n : ℝ))}`. -/
theorem step1_scaleSum_endpoint_originCube [NeZero d] {m n : ℤ} (hnm : n ≤ m)
    (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hp : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    Real.rpow
        (Ch02.HomogenizationError (originCube d m) n s .infinity (.finite 2) F a0) p ≤
      Real.rpow (2 : ℝ) p * Real.rpow (3 : ℝ) ((d : ℝ) * ((m : ℝ) - (n : ℝ))) *
        Ch02.geometricDiscount s 1 *
          ∑' l : ℕ, Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
              (fun R => Real.rpow (Ch02.normalizedBlockResponseMax R F a0) (p / 2)) := by
  have hcast : (((originCube d m).scale - n : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    show ((m - n : ℤ) : ℝ) = (m : ℝ) - (n : ℝ)
    push_cast
    ring
  have hmain := step1_scaleSum_endpoint (originCube d m) (n := n) hnm F a0 hs hs1 hp
  rw [hcast] at hmain
  exact hmain

end

end Algsuperdiff.Section4.Provider.BoundsEaL
