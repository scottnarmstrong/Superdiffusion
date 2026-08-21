/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The `G_1^a` shell group of the annular decomposition -- the square-of-sum gauge

Local helpers for ABK26, Section 4.1, the right-hand side of
`e.mathcalE.annular.decomp`.

## The square-of-sum reading

`annularG1a gamma Y k` is the **square of the `l^1` shell sum**

```
annularG1a gamma Y k = ( sum_{j >= 0} 3^(-(1-gamma) j) * Y (k+j) )^2 ,
```

i.e. the square sits **outside** the sum.  The printed display puts the square
inside; the inside-square variant cannot dominate the fifth `pre.zero` term.

## The rate cannot be doubled

`not_exists_sq_tsum_le_at_doubled_rate` is the standing guard on the shape: the
squared `l^1` shell sum at weight `3^(-cj)` is **not** dominated by any multiple
of the square sum at the *doubled* weight `3^(-2cj)`.  Cauchy-Schwarz is
saturated by the geometric family `Y_j = 3^(cj) * 1_{j<N}`.  (Every weight
`3^(-2 alpha j)` with `alpha < c` is attainable, at an amplitude blowing up as
`alpha` increases to `c`.)

## Main definitions

* `annularG1a` -- the `G_1^a` group as the square of the `l^1` shell sum.

## Main results

* `annularG1a_sqrt_eq` -- the sharp shape: `sqrt (annularG1a ...)` **is** the
  `l^1` shell sum, at the full rate `1 - gamma` and amplitude `1`.
* `annularG1a_le_sq_of_shellSum` -- the good-event bound: a bound `T` on the
  `l^1` shell sum gives `annularG1a <= T^2`.
* `not_exists_sq_tsum_le_at_doubled_rate` -- the doubled-rate square-sum shape
  is unattainable.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## The `rpow` / geometric-power bridge -/

/-- `3 ^ (-(c * j)) = (3 ^ (-c)) ^ j` for a natural `j`. -/
theorem threeRpow_neg_natMul (c : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-(c * (j : ℝ))) = ((3 : ℝ) ^ (-c)) ^ j := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-c)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-! ## The `G_1^a` shell group -/

/-- **The `G_1^a` shell group** over an abstract per-shell bracket `Y`
(the intended instantiation is the manuscript's
`3^((2-gamma) l) * ‖grad j_l‖_{W^{1,infty}(Box_l)}`):

```
annularG1a gamma Y k = ( sum_{j >= 0} 3^(-(1-gamma) j) * Y (k+j) )^2 .
```

The square is outside the sum; see the module docstring. -/
def annularG1a (gamma : ℝ) (Y : ℤ → ℝ) (k : ℤ) : ℝ :=
  (∑' j : ℕ, (3 : ℝ) ^ (-((1 - gamma) * (j : ℝ))) * Y (k + (j : ℤ))) ^ 2

theorem annularG1a_nonneg (gamma : ℝ) (Y : ℤ → ℝ) (k : ℤ) :
    0 ≤ annularG1a gamma Y k :=
  sq_nonneg _

/-- The `l^1` shell sum of an abstract nonnegative bracket is nonnegative. -/
theorem shellSum_nonneg {gamma : ℝ} {Y : ℤ → ℝ} (hY : ∀ l, 0 ≤ Y l) (k : ℤ) :
    0 ≤ ∑' j : ℕ, (3 : ℝ) ^ (-((1 - gamma) * (j : ℝ))) * Y (k + (j : ℤ)) :=
  tsum_nonneg fun j => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hY _)

/-- **The sharp shape: `sqrt (G_1^a)` IS the `l^1` shell sum**, at the full rate
`1 - gamma` and amplitude `1` -- an identity, no side condition beyond the
nonnegativity of the bracket. -/
theorem annularG1a_sqrt_eq {gamma : ℝ} {Y : ℤ → ℝ} (hY : ∀ l, 0 ≤ Y l) (k : ℤ) :
    Real.sqrt (annularG1a gamma Y k)
      = ∑' j : ℕ, (3 : ℝ) ^ (-((1 - gamma) * (j : ℝ))) * Y (k + (j : ℤ)) := by
  rw [annularG1a, Real.sqrt_sq (shellSum_nonneg (gamma := gamma) hY k)]

/-- **The good-event bound for `G_1^a`.**  A bound `T` on the `l^1` shell sum
squares to a bound on the group. -/
theorem annularG1a_le_sq_of_shellSum {gamma T : ℝ} {Y : ℤ → ℝ} {k : ℤ}
    (hY : ∀ l, 0 ≤ Y l)
    (hT : (∑' j : ℕ, (3 : ℝ) ^ (-((1 - gamma) * (j : ℝ))) * Y (k + (j : ℤ))) ≤ T) :
    annularG1a gamma Y k ≤ T ^ 2 :=
  pow_le_pow_left₀ (shellSum_nonneg (gamma := gamma) hY k) hT 2

/-! ## The doubled-rate square-sum shape is unattainable -/

/-- **The shell rate cannot be doubled.**

For every `c` there is **no** constant `A` for which the squared `l^1` shell sum
with weight `3^(-cj)` is dominated by the square sum at the *doubled* weight
`3^(-2cj)`:

```
( sum_j 3^(-cj) * Y_j )^2 <= A * sum_j 3^(-2cj) * Y_j^2      is false for all A.
```

Cauchy-Schwarz is saturated by the geometric family `Y_j = 3^(cj) * 1_{j<N}`,
for which both sums equal `N`, forcing `N <= A`.  This is the standing guard
against re-introducing a square-sum slot at the shell rate. -/
theorem not_exists_sq_tsum_le_at_doubled_rate (c : ℝ) :
    ¬ ∃ A : ℝ, ∀ Y : ℕ → ℝ, (∀ j, 0 ≤ Y j) →
      (∑' j : ℕ, (3 : ℝ) ^ (-(c * (j : ℝ))) * Y j) ^ 2
        ≤ A * ∑' j : ℕ, (3 : ℝ) ^ (-((2 * c) * (j : ℝ))) * (Y j) ^ 2 := by
  rintro ⟨A, hA⟩
  obtain ⟨N, hN⟩ := exists_nat_gt A
  set M : ℕ := N + 1 with hMdef
  have hAM : A < (M : ℝ) := by
    have hNM : (N : ℝ) < (M : ℝ) := by
      rw [hMdef]
      exact_mod_cast Nat.lt_succ_self N
    linarith only [hN, hNM]
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    rw [hMdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)
  set Y : ℕ → ℝ := fun j => if j < M then (3 : ℝ) ^ (c * (j : ℝ)) else 0 with hYdef
  have hY0 : ∀ j, 0 ≤ Y j := by
    intro j
    rw [hYdef]
    dsimp only
    split_ifs
    · exact Real.rpow_nonneg (by norm_num) _
    · exact le_rfl
  have hone : ∀ j : ℕ, (3 : ℝ) ^ (-(c * (j : ℝ))) * Y j = if j < M then (1 : ℝ) else 0 := by
    intro j
    rw [hYdef]
    dsimp only
    split_ifs with h
    · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    · ring
  have htwo : ∀ j : ℕ, (3 : ℝ) ^ (-((2 * c) * (j : ℝ))) * (Y j) ^ 2
      = if j < M then (1 : ℝ) else 0 := by
    intro j
    rw [hYdef]
    dsimp only
    split_ifs with h
    · rw [← Real.rpow_natCast ((3 : ℝ) ^ (c * (j : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        show -(2 * c * (j : ℝ)) + c * (j : ℝ) * ((2 : ℕ) : ℝ) = 0 by push_cast; ring,
        Real.rpow_zero]
    · rw [zero_pow (by norm_num), mul_zero]
  have hind : ∑' j : ℕ, (if j < M then (1 : ℝ) else 0) = (M : ℝ) := by
    rw [tsum_eq_sum (s := Finset.range M) ?_]
    · rw [Finset.sum_congr rfl (fun b hb => if_pos (Finset.mem_range.mp hb))]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · intro b hb
      simp only [Finset.mem_range] at hb
      exact if_neg hb
  have hL : (∑' j : ℕ, (3 : ℝ) ^ (-(c * (j : ℝ))) * Y j) = (M : ℝ) := by
    rw [tsum_congr hone, hind]
  have hR : (∑' j : ℕ, (3 : ℝ) ^ (-((2 * c) * (j : ℝ))) * (Y j) ^ 2) = (M : ℝ) := by
    rw [tsum_congr htwo, hind]
  have hkey := hA Y hY0
  rw [hL, hR] at hkey
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith only [hM1]
  have hprod : A * (M : ℝ) < (M : ℝ) * (M : ℝ) := mul_lt_mul_of_pos_right hAM hM0
  linarith only [hkey, hprod]

end

end Algsuperdiff.Section4.Provider.Annular
