/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFiveSubWindow
import Algsuperdiff.Section4.Provider.Regularity.StepSixHolderExponent

/-!
# `t.regularity` Step 5: `e.oscillation.iteration.result`

## The target

```text
   3^{-n'} ‖u - (u)_{U_{n'}}‖_{L̲²(U_{n'})}
     ≤ C exp( C₁^{-1} C (1-α)(m-n) )
         ( 3^{-m'} ‖u - (u)_{U_{m'}}‖_{L̲²(U_{m'})} + C · dataG )
       + C exp( C₁^{-1} C (1-α)(m-n) ) · dataH
```

for every `n', m' ∈ ℤ` with `n ≤ n' ≤ m' ≤ m`.  The right-hand shape is fixed
by what Step 6 consumes: `oscillationHolderBound_of_iterationResult`'s `hiter`
slot, at `Real.exp ((stepOne d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent
alpha n m)`.  The theorem below produces literally that expression.

## Four readings of the printed step, and where each is discharged

* The iteration lemma concludes only at the bottom index; the "for every
  `n', m'`" conclusion is the sub-window re-run with inherited budgets.  Device:
  `StepFiveSubWindow`'s `exists_oscillation_subwindow_of_iterationLemma`,
  applied here.
* The anchor demands the decay on `[n,m] \ 𝓑`, while Step 4 supplies it only on
  `[n+k, m-1] \ 𝓑_z`.  Device: `stepFiveBadSet` below,
  `𝓑 := (𝓑_z ∪ [n, n+k) ∪ {m}) ∩ [n,m]`, with
  `|𝓑| ≤ |𝓑_z| + k + 1` (`stepFiveBadSet_card_le`) priced through the anchor's
  own `exp(C(h+1)(|𝓑|+1))`.  The enlargement is carried explicitly.
* The boundary leg `ε_j ‖∇h‖_{L^∞} 1_{z∉□_{m-1}}` sits inside `δ_j`; it
  is never discarded — it travels in `dataH`, whose coefficient is tracked
  separately from `dataG`'s.
* Only conclusion (i) of the anchor (the product form) is consumed, via the
  sub-window device, which itself takes only `.1`.

## What is discharged inside, and the one conditional input

The one conditional input is the Step-4 per-scale excess decay, carried as the
hypothesis named `hstep4` and named in the theorem's name.  Its exact text
is quoted in the theorem's docstring.

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The enlarged bad set -/

/-- The missing indices are exactly `[n, n+k)` and `{m}`, so

```text
   𝓑 := ( 𝓑_z ∪ [n, n+k) ∪ {m} ) ∩ [n, m] .
```

The intersection with `[n,m]` is what makes `𝓑 ⊆ Finset.Icc n m` hold with no
side condition on `k` versus `m-n`. -/
def stepFiveBadSet (Bz : Finset ℤ) (n m : ℤ) (k : ℕ) : Finset ℤ :=
  (Bz ∪ Finset.Ico n (n + (k : ℤ)) ∪ {m}) ∩ Finset.Icc n m

/-- The enlarged bad set satisfies the anchor's binder `𝓑 ⊆ Finset.Icc n m`. -/
theorem stepFiveBadSet_subset (Bz : Finset ℤ) (n m : ℤ) (k : ℕ) :
    stepFiveBadSet Bz n m k ⊆ Finset.Icc n m :=
  Finset.inter_subset_right

/-- **The enlargement's cardinality price**: `|𝓑| ≤ |𝓑_z| + k + 1`, which the
anchor's prefactor `exp(C(h+1)(|𝓑|+1))` absorbs. -/
theorem stepFiveBadSet_card_le (Bz : Finset ℤ) (n m : ℤ) (k : ℕ) :
    (stepFiveBadSet Bz n m k).card ≤ Bz.card + k + 1 := by
  have h1 : (stepFiveBadSet Bz n m k).card ≤
      (Bz ∪ Finset.Ico n (n + (k : ℤ)) ∪ {m}).card :=
    Finset.card_le_card Finset.inter_subset_left
  have h2 : (Bz ∪ Finset.Ico n (n + (k : ℤ)) ∪ {m}).card ≤
      (Bz ∪ Finset.Ico n (n + (k : ℤ))).card + ({m} : Finset ℤ).card :=
    Finset.card_union_le _ _
  have h3 : (Bz ∪ Finset.Ico n (n + (k : ℤ))).card ≤
      Bz.card + (Finset.Ico n (n + (k : ℤ))).card :=
    Finset.card_union_le _ _
  have h4 : (Finset.Ico n (n + (k : ℤ))).card = k := by
    rw [Int.card_Ico]
    omega
  have h5 : ({m} : Finset ℤ).card = 1 := Finset.card_singleton m
  omega

theorem iterationDecay_of_stepFourDecay {U : ℤ → Set (Vec d)} {u : Vec d → ℝ}
    {g : ℤ → Vec d} {θ : ℝ} {ε δ : ℤ → ℝ} {Bz : Finset ℤ} {n m : ℤ} {k : ℕ}
    (hstep4 : ∀ j : ℤ, n + (k : ℤ) ≤ j → j ≤ m - 1 → j ∉ Bz →
      affineExcess (U (j - (k : ℤ))) u ≤
        θ ^ k * affineExcess (U j) u + ε j * slopeMagnitude (g j) + δ j) :
    IterationDecay U u g k θ ε δ (stepFiveBadSet Bz n m k) n m := by
  intro j hjn hjm hjB
  have hmem : j ∈ Finset.Icc n m := Finset.mem_Icc.mpr ⟨hjn, hjm⟩
  have hnot : j ∉ Bz ∪ Finset.Ico n (n + (k : ℤ)) ∪ {m} := by
    intro hc
    exact hjB (Finset.mem_inter.mpr ⟨hc, hmem⟩)
  have hnotBz : j ∉ Bz := fun hc =>
    hnot (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
  have hnotIco : j ∉ Finset.Ico n (n + (k : ℤ)) := fun hc =>
    hnot (Finset.mem_union_left _ (Finset.mem_union_right _ hc))
  have hnotm : j ≠ m := by
    intro hc
    exact hnot (Finset.mem_union_right _ (Finset.mem_singleton.mpr hc))
  have hge : n + (k : ℤ) ≤ j := by
    by_contra hc
    exact hnotIco (Finset.mem_Ico.mpr ⟨hjn, by omega⟩)
  exact hstep4 j hge (by omega) hnotBz

/-! ## 2. The contraction parameters `θ = 3^{-1/4}`, `h = k` -/

/-- **`θ := 3^{-1/4}`**, the iteration lemma's contraction ratio at Step 5. -/
def stepFiveTheta : ℝ := (3 : ℝ) ^ (-(1 / 4) : ℝ)

/-- `θ ∈ (0,1)` — the anchor's first `θ`-binder. -/
theorem stepFiveTheta_mem : stepFiveTheta ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- `θ^k = 3^{-k/4}`: the natural-power/`rpow` bridge the anchor's second
`θ`-binder needs. -/
theorem stepFiveTheta_pow (k : ℕ) :
    stepFiveTheta ^ k = (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) := by
  rw [stepFiveTheta, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 4) : ℝ)) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- `3^{-1/2} < 3/5`, i.e. `25 < 27`. -/
theorem three_rpow_neg_half_lt : (3 : ℝ) ^ (-(1 / 2) : ℝ) < 3 / 5 := by
  have hsq : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hgt : (5 / 3 : ℝ) < Real.sqrt 3 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ (5 / 3 : ℝ) ^ 2)
      (by norm_num : ((5 / 3 : ℝ)) ^ 2 < 3)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 3)] at h
  have hone : (1 : ℝ) < 3 / 5 * Real.sqrt 3 := by linarith only [hgt]
  have hkey : (1 : ℝ) / Real.sqrt 3 < 3 / 5 := (div_lt_iff₀ hsq).mpr hone
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), ← Real.sqrt_eq_rpow,
    inv_eq_one_div]
  exact hkey

/-- `θ^k ∈ (0, 3/5)` for `k ≥ 2` — the anchor's second `θ`-binder.  's
`stepOneK_ge_ten` supplies `k ≥ 10 ≥ 2` a fortiori. -/
theorem stepFiveTheta_pow_mem {k : ℕ} (hk : 2 ≤ k) :
    stepFiveTheta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) := by
  rw [stepFiveTheta_pow]
  constructor
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hexp : -(1 / 4 : ℝ) * (k : ℝ) ≤ -(1 / 2 : ℝ) := by linarith only [hkr]
    have hmono : (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) ≤ (3 : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    exact lt_of_le_of_lt hmono three_rpow_neg_half_lt

/-! ## 3. The prefactor conversion, over abstract reals -/

/-- The additive budget bound behind the prefactor conversion: with
`|𝓑|+1 ≤ K₁ + K₂ X` and `∑ε ≤ K₃ X`,

```text
   C₀(h+1)(|𝓑|+1) + C₀ ∑ε  ≤  C₀(h+1)K₁ + ( C₀(h+1)K₂ + C₀K₃ ) X .
```

Abstract reals only. -/
theorem exp_budget_bound {C0 hR Bc Se K1 K2 K3 X : ℝ} (hC0 : 0 ≤ C0)
    (hhR : 0 ≤ hR) (hB : Bc + 1 ≤ K1 + K2 * X) (hS : Se ≤ K3 * X) :
    C0 * (hR + 1) * (Bc + 1) + C0 * Se ≤
      C0 * (hR + 1) * K1 + (C0 * (hR + 1) * K2 + C0 * K3) * X := by
  have hc : 0 ≤ C0 * (hR + 1) := mul_nonneg hC0 (by linarith only [hhR])
  have h1 := mul_le_mul_of_nonneg_left hB hc
  have h2 := mul_le_mul_of_nonneg_left hS hC0
  linarith only [h1, h2]

/-- The exponential form of the same: the anchor's ADDITIVE prefactor is dominated
by a times `exp` of the Step-6 exponent. -/
theorem exp_budget_le_mul_exp {C0 hR Bc Se K1 K2 K3 X : ℝ} (hC0 : 0 ≤ C0)
    (hhR : 0 ≤ hR) (hB : Bc + 1 ≤ K1 + K2 * X) (hS : Se ≤ K3 * X) :
    Real.exp (C0 * (hR + 1) * (Bc + 1) + C0 * Se) ≤
      Real.exp (C0 * (hR + 1) * K1) *
        Real.exp ((C0 * (hR + 1) * K2 + C0 * K3) * X) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (exp_budget_bound hC0 hhR hB hS)

/-! ## 4. The shape of `e.oscillation.iteration.result`, over abstract reals -/

/-- The scalar core of the composition into Step 6's `hiter` shape: no `exp`, no
`rpow`, every atom an abstract real.  `Eq` is the anchor's prefactor, `Q` the
Step-6 exponential, `Sd` the `δ`-sum. -/
theorem oscillation_shape_aux {C Cpre Cg Ch Eq Q oscLo oscHi dataG dataH Sd : ℝ}
    (hEq : 0 ≤ Eq) (hQ : 0 ≤ Q) (hoscHi : 0 ≤ oscHi) (hdataG : 0 ≤ dataG)
    (hdataH : 0 ≤ dataH) (hCg0 : 0 ≤ Cg) (hCh0 : 0 ≤ Ch)
    (hSd : Sd ≤ Cg * dataG + Ch * dataH) (hpre : Eq ≤ Cpre * Q)
    (hCpre : Cpre ≤ C) (hCgC : Cpre * Cg ≤ C * C) (hChC : Cpre * Ch ≤ C)
    (hiter : oscLo ≤ Eq * (oscHi + Sd)) :
    oscLo ≤ C * Q * (oscHi + C * dataG) + C * Q * dataH := by
  have hbr : 0 ≤ oscHi + (Cg * dataG + Ch * dataH) := by
    have hg := mul_nonneg hCg0 hdataG
    have hh := mul_nonneg hCh0 hdataH
    linarith only [hoscHi, hg, hh]
  have s1 : Eq * (oscHi + Sd) ≤ Eq * (oscHi + (Cg * dataG + Ch * dataH)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hSd]) hEq
  have s2 : Eq * (oscHi + (Cg * dataG + Ch * dataH)) ≤
      Cpre * Q * (oscHi + (Cg * dataG + Ch * dataH)) :=
    mul_le_mul_of_nonneg_right hpre hbr
  have t1 : Cpre * Q * oscHi ≤ C * Q * oscHi := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpre hQ) hoscHi
    linarith only [h]
  have t2 : Cpre * Cg * (Q * dataG) ≤ C * C * (Q * dataG) :=
    mul_le_mul_of_nonneg_right hCgC (mul_nonneg hQ hdataG)
  have t3 : Cpre * Ch * (Q * dataH) ≤ C * (Q * dataH) :=
    mul_le_mul_of_nonneg_right hChC (mul_nonneg hQ hdataH)
  have hexpand : Cpre * Q * (oscHi + (Cg * dataG + Ch * dataH))
      = Cpre * Q * oscHi + Cpre * Cg * (Q * dataG) + Cpre * Ch * (Q * dataH) := by
    ring
  have htarget : C * Q * (oscHi + C * dataG) + C * Q * dataH
      = C * Q * oscHi + C * C * (Q * dataG) + C * (Q * dataH) := by ring
  linarith only [hiter, s1, s2, t1, t2, t3, hexpand, htarget]

/-! ## 5. `e.oscillation.iteration.result` -/

/-- **`e.oscillation.iteration.result`**, assembled at the shape Step 6 consumes.

For every `n', m'` with `n ≤ n' ≤ m' ≤ m`,

```text
   3^{-n'} ‖u - (u)_{U_{n'}}‖_{L̲²(U_{n'})}
     ≤ C exp( C₁^{-1} C_iter (1-α)(m-n) ) ( 3^{-m'} ‖u - (u)_{U_{m'}}‖ + C·dataG )
       + C exp( C₁^{-1} C_iter (1-α)(m-n) ) · dataH ,
```

with `C₁ = stepOne d Cedos Cann C_iter k` and the exponent written as
`stepSixExponent alpha n m`, so that
`oscillationHolderBound_of_iterationResult` unifies with it directly.  The
produced constants are explicit:

```text
   C_iter := 2 C₀ (k+2) ,      C := max 1 exp( C₀ (k+1)(k+2) ) ,
```

`C₀` being the frozen iteration anchor's own constant.

```lean
   ∀ j : ℤ, n + (k : ℤ) ≤ j → j ≤ m - 1 → j ∉ Bz →
     affineExcess (U (j - (k : ℤ))) u ≤
       stepFiveTheta ^ k * affineExcess (U j) u +
         ε j * slopeMagnitude (g j) + δ j
```

i.e. `e.Ej.decay.assumption` at `h := k`, `θ := 3^{-1/4}`, the Step-5 `ε_j`,
`δ_j`, and the bad set `𝓑_z` — on Step 4's OWN range `[n+k, m-1] \ 𝓑_z`.

Every other hypothesis is a source premise of the node: the anchor's binders,
the Step-3 budget `|𝓑_z| ≤ δ(m-n+1)`, `e.sum.eps.j.bound` (supplied by
`StepFiveBudgetSums.sum_stepFiveEps_le_two_mul_delta_mul_window`),
`e.sum.delta.j.bound` (supplied by `StepFiveBudgetSums.sum_Icc_delta_le_of_legs`
together with `StepFiveShomComparison`), and the regime `α ≤ 1`, `1 ≤ m-n`. -/
theorem oscillationIterationResult_of_stepFourDecay (d : ℕ) (hd : d ≠ 0) (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ C Citer : ℝ, 0 < C ∧ 0 ≤ Citer ∧
      ∀ (Cedos Cann alpha : ℝ), alpha ≤ 1 →
        ∀ n m : ℤ, (1 : ℤ) ≤ m - n →
          ∀ U : ℤ → Set (Vec d), IterationWindowFamily U m →
            ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (U m)) →
              ∀ (c : ℤ → ℝ) (g : ℤ → Vec d),
                (∀ j : ℤ, j ≤ m → IsAffineMinimizer (U j) u (c j) (g j)) →
                  ∀ Bz : Finset ℤ,
                    (Bz.card : ℝ) ≤
                        stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
                          (((m : ℝ) - (n : ℝ)) + 1) →
                      ∀ ε δ : ℤ → ℝ,
                        (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ ε j) →
                        (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ δ j) →
                        (∑ j ∈ Finset.Icc n m, ε j ≤
                          2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
                            ((m : ℝ) - (n : ℝ))) →
                        ∀ dataG dataH : ℝ, 0 ≤ dataG → 0 ≤ dataH →
                          (∑ j ∈ Finset.Icc n m, δ j ≤ dataG + dataH) →
                          (∀ j : ℤ, n + (k : ℤ) ≤ j → j ≤ m - 1 → j ∉ Bz →
                            affineExcess (U (j - (k : ℤ))) u ≤
                              stepFiveTheta ^ k * affineExcess (U j) u +
                                ε j * slopeMagnitude (g j) + δ j) →
                          ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
                            (3 : ℝ) ^ (-n') *
                                normalizedL2On (U n')
                                  (fun x => u x - volumeAverage (U n') u) ≤
                              C *
                                  Real.exp
                                    ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
                                      stepSixExponent alpha n m) *
                                  ((3 : ℝ) ^ (-m') *
                                      normalizedL2On (U m')
                                        (fun x => u x - volumeAverage (U m') u) +
                                    C * dataG) +
                                C *
                                  Real.exp
                                    ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
                                      stepSixExponent alpha n m) * dataH := by
  obtain ⟨C0, hC0, hsub⟩ := exists_oscillation_subwindow_of_iterationLemma d hd
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine ⟨max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))), 2 * C0 * ((k : ℝ) + 2),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    mul_nonneg (mul_nonneg (by norm_num) hC0.le) (by linarith only [hkR]), ?_⟩
  intro Cedos Cann alpha halpha n m hwin U hU u hu c g hmin Bz hBz ε δ hε hδ hSe
    dataG dataH hdataG hdataH hSd hstep4 n' m' hn' hn'm' hm'm
  have hnm : n ≤ m := by omega
  have hmnR : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have hcast : ((1 : ℤ) : ℝ) ≤ ((m - n : ℤ) : ℝ) := Int.cast_le.mpr hwin
    push_cast at hcast
    linarith only [hcast]
  have hC1pos : 0 < stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k :=
    stepOneC1_pos d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k
  have hdpar : 0 ≤ stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha := by
    simp only [stepOneDelta]
    exact mul_nonneg (inv_nonneg.mpr hC1pos.le) (by linarith only [halpha])
  -- the Step-6 exponent slot, and the abbreviation `X` for `δ (m-n)`
  have hXnn : 0 ≤ stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
      ((m : ℝ) - (n : ℝ)) := mul_nonneg hdpar (by linarith only [hmnR])
  have hcardR : (((stepFiveBadSet Bz n m k).card : ℝ)) ≤ (Bz.card : ℝ) + (k : ℝ) + 1 := by
    have h := stepFiveBadSet_card_le Bz n m k
    exact_mod_cast h
  have hgrow : stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
      (((m : ℝ) - (n : ℝ)) + 1) ≤
      2 * (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
        ((m : ℝ) - (n : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left
      (show ((m : ℝ) - (n : ℝ)) + 1 ≤ 2 * ((m : ℝ) - (n : ℝ)) by linarith only [hmnR]) hdpar
    linarith only [h]
  have hBc : (((stepFiveBadSet Bz n m k).card : ℝ)) + 1 ≤
      ((k : ℝ) + 2) +
        2 * (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
          ((m : ℝ) - (n : ℝ))) := by
    linarith only [hcardR, hBz, hgrow]
  have hSeX : (∑ j ∈ Finset.Icc n m, ε j) ≤
      2 * (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
        ((m : ℝ) - (n : ℝ))) := by
    have hid : 2 * stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
        ((m : ℝ) - (n : ℝ)) =
        2 * (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
          ((m : ℝ) - (n : ℝ))) := by ring
    linarith only [hSe, hid]
  -- the sub-window run of the anchor, at the enlarged bad set
  have hrun := hsub k stepFiveTheta stepFiveTheta_mem (stepFiveTheta_pow_mem hk) n m hnm U hU
    u hu (stepFiveBadSet Bz n m k) (stepFiveBadSet_subset Bz n m k) ε δ hε hδ c g hmin
    (iterationDecay_of_stepFourDecay hstep4) n' m' hn' hn'm' hm'm
  -- the prefactor conversion
  have hpre0 := exp_budget_le_mul_exp (C0 := C0) (hR := (k : ℝ))
    (Bc := ((stepFiveBadSet Bz n m k).card : ℝ))
    (Se := ∑ j ∈ Finset.Icc n m, ε j) (K1 := (k : ℝ) + 2) (K2 := 2) (K3 := 2)
    (X := stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
      ((m : ℝ) - (n : ℝ))) hC0.le hkR hBc hSeX
  have hQeq : (C0 * ((k : ℝ) + 1) * 2 + C0 * 2) *
      (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k) alpha *
        ((m : ℝ) - (n : ℝ)))
      = (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 2)) k)⁻¹ *
          (2 * C0 * ((k : ℝ) + 2)) * stepSixExponent alpha n m := by
    simp only [stepOneDelta, stepSixExponent]
    ring
  rw [hQeq] at hpre0
  refine oscillation_shape_aux (Cg := 1) (Ch := 1)
    (Cpre := Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2)))
    (Real.exp_pos _).le (Real.exp_pos _).le
    (mul_nonneg (zpow_nonneg (by norm_num) _) (normalizedL2On_nonneg _ _))
    hdataG hdataH zero_le_one zero_le_one (by linarith only [hSd]) hpre0
    (le_max_right _ _) ?_ ?_ hrun
  · have h1 : (1 : ℝ) ≤ max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) :=
      le_max_left _ _
    have h2 : Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
        max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_left h1
      (show (0 : ℝ) ≤ max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) by
        linarith only [h1])
    linarith only [h2, h3]
  · have h2 : Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
        max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) := le_max_right _ _
    linarith only [h2]

end

end Algsuperdiff.Section4.Provider.Regularity
