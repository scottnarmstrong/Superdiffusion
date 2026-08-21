/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomStepTwoLocal

/-!
# Theorem B, §4.5, Step 3a/3b: the gradient homogenization bound and
# the weak gradient bound

## The two targets

Step 3 (the coarse graining application): substitute the mesoscale energy bound
(the Step 2b) into the general coarse-graining estimate and obtain the gradient
homogenization bound.

Step 3 (the gap absorption): the mesoscale gap `s^{-9/2} 3^{(n-m)/2} ≤ C γ^5`,
substituted back, compared with the definition of `EthmB(m)`, yielding the weak
gradient bound.

## THE SECOND CONDITIONAL EDGE — disclosed

The general coarse-graining proposition is a declared dependency AND a declared
source hypothesis of the Step-3a node ("the general coarse-graining proposition
applied with `p → ∞` … substituted into the general coarse-graining estimate"),
so its conclusion enters here as a NAMED TRANSCRIBED HYPOTHESIS `hCG`, exactly
as Theorem C's display enters as `hC`.  It is **not** available as a theorem:

* the graph marks the node a BOUNDARY LEAF (Section 2, out of this lane) with
  `LEAN_STATUS: NOT_STARTED`;
* `CoarseGraining`'s relative, `Ch03.generalCoarseGrainingL2TwoExponentTheory`, is the
  **`p = 2` / negative-Besov-`L²`** package
  (`homogenizationComparisonNegativeBesovLHS`), not the `W̲^{-s,∞}` object this
  step needs;
* it is recorded that the literal endpoint `p = ∞` is UNAVAILABLE from the
  source (the dual exponent `p' = 1` breaks the flat-cube CZ estimate behind
  the Calderón--Zygmund flux comparison lemma), and neither a `p`-uniformity remark on `C(p,d)` nor an
  explicit large-`q` conclusion is given.

Everything in the passage OTHER than that Proposition is proved here, with the
`p → ∞` reading of its display transcribed verbatim in the `hCG` binder.  The
`W̲^{-s,∞}` left-hand side is carried as the abstract nonnegative real `L`, so
nothing about the negative-norm carrier is assumed either.

## What is proved

1. **The sup collapse** (`stepThreeSupBound`): every member of the weighted
   family the Proposition's first term takes a supremum of is bounded by
   `C_meso · (Step-2 majorant)` — this is the
   `stepTwoLocal_sectionFive`, so the Proposition may be read at that slot.
2. **The `σ̄` bookkeeping** (`sqrt_mul_homStepTwoMajorant`), the node's own NOTE:
   `σ̄^{1/2}(σ̄^{-1/2}3^{m/2} + σ̄^{1/2}3^{m/2}) = 3^{m/2} + σ̄ 3^{m/2}`, an exact
   identity — the manuscript performs it silently.
3. **The side condition** (`inv_half_sub_le_four`): `(s₂-s)^{-1} ≤ 4` at
   `s₂ = 1/2`, `s ≤ 1/4`.  The correction says the manuscript absorbs this factor
   with no stated side condition; here the condition is a hypothesis and the
   numeral `4` is displayed.
4. **The forcing leg at `s₂ = 1/2`** (`three_rpow_mesoscale_data_le`):
   `3^{s₂ n}[g]_{W̲^{s₂,∞}} ≤ K_g 3^{(n-m)/2} 3^{m/2}`, an exact `3`-power split
   plus the §4.5 normalization.  This is where the second term's `3^{(n-m)/2}`
   comes from.
5. **Step 3a** (`stepThreeCoarseGraining_of_display`): items 1--4 assembled into
   the gradient homogenization bound.
6. **The gap absorption** (`homGapAbsorb`)'s "`gapAbsorb`
   computation": `s^{-9/2}3^{(n-m)/2} ≤ C_gap0(d-free) γ^5` with the EXPLICIT
   constant `C_gap0 = (log 3 - 1)^{-5}`.  `5 log 3 = 5.49… > 5` is genuine and is
   exactly the slack the proof spends; the elementary lever is `t ≤ exp t`
   applied at `t = (log 3 - 1) |log γ|`, no series and no factorials.
7. **Step 3b** (`stepThreeWeakGradientBound`): substitute 6 into 5, divide by
   `σ̄_m` (the node's "silent but arithmetically exact" division) and compare
   with the two summands of `EthmB(m)`, giving the weak gradient bound.
8. **The `EthmB` comparison, machine-visible** (`ethmB_ge_first_summand`,
   together with the `ethmB_ge_gap`): the two summands the Step-3b
   comparison consumes really are below the `EthmB` carrier.
-/

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Step 2's majorant and the `σ̄` bookkeeping -/

/-- **The Step-2 majorant** — the right-hand side of the mesoscale energy bound
stripped of its `3^{(1-α)(m-j)}` weight:

```
  C 3^{(1-α)X_m(α)} (1 + 𝓔_{1/4,∞,2}) ( σ̄_m^{-1/2} 3^{m/2} + σ̄_m^{1/2} 3^{m/2} ).
```

`Xfac` is the minimal-scale factor `3^{(1-α)X_m(α)}` as a single nonnegative
real; nothing here depends on how it is built. -/
def homStepTwoMajorant (Cr Xfac Eq sigma : ℝ) (m : ℤ) : ℝ :=
  Cr * Xfac * (1 + Eq) *
    (Real.sqrt sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) +
      Real.sqrt sigma * (3 : ℝ) ^ ((m : ℝ) / 2))

theorem homStepTwoMajorant_nonneg {Cr Xfac Eq sigma : ℝ} (hCr : 0 ≤ Cr) (hXfac : 0 ≤ Xfac)
    (hEq : 0 ≤ Eq) (m : ℤ) : 0 ≤ homStepTwoMajorant Cr Xfac Eq sigma m := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hsum : (0 : ℝ) ≤ Real.sqrt sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) +
      Real.sqrt sigma * (3 : ℝ) ^ ((m : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ Real.sqrt sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) :=
      mul_nonneg (Real.sqrt_nonneg _) h3
    have h2 : (0 : ℝ) ≤ Real.sqrt sigma * (3 : ℝ) ^ ((m : ℝ) / 2) :=
      mul_nonneg (Real.sqrt_nonneg _) h3
    linarith only [h1, h2]
  rw [homStepTwoMajorant]
  exact mul_nonneg (mul_nonneg (mul_nonneg hCr hXfac) (by linarith only [hEq])) hsum

/-- **The `σ̄` bookkeeping of Step 3a**, exact.  The Proposition's first term
carries `σ̄_m^{1/2}` in front; Step 2's majorant carries `σ̄_m^{∓1/2}` inside; the
product is the printed `3^{m/2} + σ̄_m 3^{m/2}`.  The manuscript performs this
silently (the node's own NOTE). -/
theorem sqrt_mul_homStepTwoMajorant (Cr Xfac Eq : ℝ) {sigma : ℝ} (hsigma : 0 < sigma)
    (m : ℤ) :
    Real.sqrt sigma * homStepTwoMajorant Cr Xfac Eq sigma m =
      Cr * Xfac * (1 + Eq) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2)) := by
  have hinv : Real.sqrt sigma * Real.sqrt sigma⁻¹ = 1 := by
    rw [← Real.sqrt_mul hsigma.le, mul_inv_cancel₀ (ne_of_gt hsigma), Real.sqrt_one]
  have hsq : Real.sqrt sigma * Real.sqrt sigma = sigma := Real.mul_self_sqrt hsigma.le
  rw [homStepTwoMajorant]
  calc Real.sqrt sigma *
        (Cr * Xfac * (1 + Eq) *
          (Real.sqrt sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) +
            Real.sqrt sigma * (3 : ℝ) ^ ((m : ℝ) / 2)))
      = Cr * Xfac * (1 + Eq) *
          ((Real.sqrt sigma * Real.sqrt sigma⁻¹) * (3 : ℝ) ^ ((m : ℝ) / 2) +
            (Real.sqrt sigma * Real.sqrt sigma) * (3 : ℝ) ^ ((m : ℝ) / 2)) := by ring
    _ = Cr * Xfac * (1 + Eq) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2)) := by
        rw [hinv, hsq, one_mul]

/-! ## 2. The two side computations of the Proposition's second term -/

/-- **The correction, made explicit**: at `s₂ = 1/2` and `s ≤ 1/4` the factor
`(s₂ - s)^{-1}` the manuscript absorbs into `C` is at most `4`. -/
theorem inv_half_sub_le_four {s : ℝ} (hs : s ≤ 1 / 4) : (1 / 2 - s)⁻¹ ≤ 4 := by
  have hpos : (0 : ℝ) < 1 / 2 - s := by linarith only [hs]
  rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 4)]
  linarith only [hs]

/-- **The forcing leg at the mesoscale.**  With `s₂ = 1/2` (the parameter web)
and the §4.5 normalization `[g]_{W̲^{1/2,∞}(□_m)} ≤ K_g`,

```
  3^{s₂ n} [g]_{W̲^{s₂,∞}(□_m)} ≤ K_g · 3^{(n-m)/2} · 3^{m/2},
```

an exact `3`-power split.  This is where the second term's `3^{(n-m)/2}` — the
factor the gap absorption then eats — comes from. -/
theorem three_rpow_mesoscale_data_le {m n : ℤ} {Dg Kg : ℝ} (hDg : Dg ≤ Kg) :
    (3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) * Dg ≤
      Kg * ((3 : ℝ) ^ (((n : ℝ) - (m : ℝ)) / 2) * (3 : ℝ) ^ ((m : ℝ) / 2)) := by
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsplit : (3 : ℝ) ^ (((n : ℝ) - (m : ℝ)) / 2) * (3 : ℝ) ^ ((m : ℝ) / 2) =
      (3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsplit]
  calc (3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) * Dg
      ≤ (3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) * Kg := mul_le_mul_of_nonneg_left hDg hw
    _ = Kg * (3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by ring

/-! ## 3. Step 3a -/

/-- **The sup slot of the Proposition, filled by Step 2b.**  Every member of the
weighted family `3^{-(s-s₁)(n-j)} ν^{1/2}‖∇u‖_{L̲²(z+□_j)}` is at most
`C_meso · (Step-2 majorant)`; this is the `stepTwoLocal_sectionFive`
read at the majorant. -/
theorem stepThreeSupBound {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|) {m : ℤ}
    {Cr Xfac Eq sigma : ℝ} (hCr : 0 ≤ Cr) (hXfac : 0 ≤ Xfac) (hEq : 0 ≤ Eq)
    {F : ℤ → Vec d → ℝ}
    (hC : ∀ j : ℤ, j ≤ m → ∀ z : Vec d,
      F j z ≤ homStepTwoMajorant Cr Xfac Eq sigma m *
        Real.rpow 3 ((1 - homAlpha M) * ((m : ℝ) - (j : ℝ)))) :
    ∀ j : ℤ, j ≤ homN M m → ∀ z : Vec d,
      Real.rpow 3 (-((homS M - homS M / 2) * (((homN M m : ℤ) : ℝ) - (j : ℝ)))) * F j z ≤
        homMesoConst * homStepTwoMajorant Cr Xfac Eq sigma m := by
  intro j hjn z
  exact stepTwoLocal_sectionFive hlog
    (homStepTwoMajorant_nonneg hCr hXfac hEq m) hC hjn z

/-- **Step 3a — the gradient homogenization bound.**

The transcribed Proposition display `hCG` (see the module docstring: this is
the one input outside the set, `p → ∞`) with Step 2b's family bound `hC`
substituted into its supremum slot and the §4.5 normalization `hDg` substituted
into its forcing slot.  The output is the printed display, with

* the first term at `(3^{m/2} + σ̄_m 3^{m/2})` — the exact `σ̄` bookkeeping;
* the second term at `s^{-9/2} 3^{(n-m)/2} · 3^{m/2}` — the shape Step 3b eats;
* the constants `C_cg · C_meso · C_r` and `4 · C_cg · K_g` DISPLAYED, not
  absorbed. -/
theorem stepThreeCoarseGraining_of_display {M : ABKModel d}
    (hlog : 4 ≤ |Real.log M.gamma|) {m : ℤ}
    {Ccg Cr Xfac E1 Eq E2 sigma Dg Kg L : ℝ} (hCcg : 0 ≤ Ccg) (hCr : 0 ≤ Cr)
    (hXfac : 0 ≤ Xfac) (hE1 : 0 ≤ E1) (hEq : 0 ≤ Eq) (hsigma : 0 < sigma)
    (hDg : Dg ≤ Kg) (hKg : 0 ≤ Kg) {F : ℤ → Vec d → ℝ}
    (hC : ∀ j : ℤ, j ≤ m → ∀ z : Vec d,
      F j z ≤ homStepTwoMajorant Cr Xfac Eq sigma m *
        Real.rpow 3 ((1 - homAlpha M) * ((m : ℝ) - (j : ℝ))))
    (hCG : ∀ S : ℝ,
      (∀ j : ℤ, j ≤ homN M m → ∀ z : Vec d,
        Real.rpow 3 (-((homS M - homS M / 2) * (((homN M m : ℤ) : ℝ) - (j : ℝ)))) *
          F j z ≤ S) →
      L ≤ Ccg * (homS M)⁻¹ * Real.sqrt sigma * E1 * S +
        Ccg * homS M ^ (-(9 / 2) : ℝ) * (1 / 2 - homS M)⁻¹ *
          (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ ((1 / 2 : ℝ) * (((homN M m : ℤ) : ℝ))) * Dg)) :
    L ≤ (Ccg * homMesoConst * Cr) * ((homS M)⁻¹ * Xfac * E1 * (1 + Eq)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2)) +
        (4 * Ccg * Kg) *
          (homS M ^ (-(9 / 2) : ℝ) *
            (3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2)) *
          (1 + E2 ^ (2 : ℕ)) * (3 : ℝ) ^ ((m : ℝ) / 2) := by
  have hlog0 : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hlog]
  have hspos : 0 < homS M := homS_pos hlog0
  have hsq : homS M ≤ 1 / 4 := homS_le_quarter hlog
  have hmain := hCG _ (stepThreeSupBound hlog hCr hXfac hEq hC)
  refine hmain.trans (add_le_add ?_ ?_)
  · /- the first term: the `σ̄` bookkeepi -/
    have hfac : (0 : ℝ) ≤ Ccg * (homS M)⁻¹ * E1 :=
      mul_nonneg (mul_nonneg hCcg (inv_nonneg.mpr hspos.le)) hE1
    have hidn : Ccg * (homS M)⁻¹ * Real.sqrt sigma * E1 *
        (homMesoConst * homStepTwoMajorant Cr Xfac Eq sigma m) =
        (Ccg * (homS M)⁻¹ * E1) * homMesoConst *
          (Real.sqrt sigma * homStepTwoMajorant Cr Xfac Eq sigma m) := by ring
    rw [hidn, sqrt_mul_homStepTwoMajorant Cr Xfac Eq hsigma m]
    exact le_of_eq (by ring)
  · /- the second term: and the mesoscale forcing spl -/
    have hspow : (0 : ℝ) ≤ homS M ^ (-(9 / 2) : ℝ) :=
      Real.rpow_nonneg hspos.le _
    have hE2sq : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by
      have hsq : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := sq_nonneg E2
      linarith only [hsq]
    have hgap : (0 : ℝ) ≤ (3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hm : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hdata := three_rpow_mesoscale_data_le (m := m) (n := homN M m) hDg
    have hinv := inv_half_sub_le_four hsq
    have hAnn : (0 : ℝ) ≤ Ccg * homS M ^ (-(9 / 2) : ℝ) :=
      mul_nonneg hCcg hspow
    have hstep1 : Ccg * homS M ^ (-(9 / 2) : ℝ) * (1 / 2 - homS M)⁻¹ *
        (1 + E2 ^ (2 : ℕ)) *
        ((3 : ℝ) ^ ((1 / 2 : ℝ) * (((homN M m : ℤ) : ℝ))) * Dg) ≤
        Ccg * homS M ^ (-(9 / 2) : ℝ) * 4 * (1 + E2 ^ (2 : ℕ)) *
          (Kg * ((3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2) *
            (3 : ℝ) ^ ((m : ℝ) / 2))) := by
      have hL : Ccg * homS M ^ (-(9 / 2) : ℝ) * (1 / 2 - homS M)⁻¹ *
          (1 + E2 ^ (2 : ℕ)) ≤
          Ccg * homS M ^ (-(9 / 2) : ℝ) * 4 * (1 + E2 ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hAnn) hE2sq
      have hRnn : (0 : ℝ) ≤ Kg * ((3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2) *
          (3 : ℝ) ^ ((m : ℝ) / 2)) := mul_nonneg hKg (mul_nonneg hgap hm)
      have hLnn : (0 : ℝ) ≤ Ccg * homS M ^ (-(9 / 2) : ℝ) *
          (1 / 2 - homS M)⁻¹ * (1 + E2 ^ (2 : ℕ)) := by
        have hpos : (0 : ℝ) < 1 / 2 - homS M := by linarith only [hsq]
        exact mul_nonneg (mul_nonneg hAnn (inv_nonneg.mpr hpos.le)) hE2sq
      exact le_trans (mul_le_mul_of_nonneg_left hdata hLnn)
        (mul_le_mul_of_nonneg_right hL hRnn)
    exact hstep1.trans (le_of_eq (by ring))

/-! ## 4. Step 3b: the gap absorption -/

/-- The gap-absorption constant `C_gap0 = (log 3 - 1)^{-5}`, explicit and
dimension-free. -/
def homGapConst : ℝ := (Real.log 3 - 1)⁻¹ ^ (5 : ℕ)

theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have he : Real.exp 1 < 3 := by
    have h := Real.exp_one_lt_d9
    linarith only [h]
  have h := Real.log_lt_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at h

theorem homGapConst_pos : 0 < homGapConst := by
  have h : (0 : ℝ) < Real.log 3 - 1 := by linarith only [one_lt_log_three]
  rw [homGapConst]
  exact pow_pos (inv_pos.mpr h) 5

/-- The elementary lever: `t ≤ exp t` at `t/5`, raised to the fifth power.  No
series, no factorials. -/
theorem pow_five_le_exp {t : ℝ} (ht : 0 ≤ t) : t ^ (5 : ℕ) ≤ 3125 * Real.exp t := by
  have hbase : t / 5 ≤ Real.exp (t / 5) := by
    have h := Real.add_one_le_exp (t / 5)
    linarith only [h]
  have hpow : (t / 5) ^ (5 : ℕ) ≤ (Real.exp (t / 5)) ^ (5 : ℕ) :=
    pow_le_pow_left₀ (by linarith only [ht]) hbase 5
  have hexp : (Real.exp (t / 5)) ^ (5 : ℕ) = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpow
  have hdiv : (t / 5) ^ (5 : ℕ) = t ^ (5 : ℕ) / 3125 := by
    rw [div_pow]
    norm_num
  rw [hdiv] at hpow
  linarith only [hpow]

/-- **The gap absorption**.

```
  s^{-9/2} 3^{(n-m)/2} ≤ C_gap0 γ^5,      C_gap0 = (log 3 - 1)^{-5}.
```

The manuscript's chain is `≤ C γ^{5 log 3}|log γ|^{9/2} ≤ C γ^5`; the slack is
exactly `5 log 3 - 5 = 5(log 3 - 1) > 0` (the node's NOTE: "`5 log 3 = 5.49… >
5`, so the last inequality is genuine"), and it is spent through
`pow_five_le_exp` at `t = 5(log 3 - 1)|log γ|`.  Both `|log γ|^{9/2} ≤ |log γ|^5`
(valid since `|log γ| ≥ 4 ≥ 1`) and `k ≥ 10|log γ|` are used, and nothing else. -/
theorem homGapAbsorb {M : ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (m : ℤ) :
    homS M ^ (-(9 / 2) : ℝ) *
        (3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2) ≤
      homGapConst * M.gamma ^ (5 : ℕ) := by
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hlog0 : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hlog]
  have hlogneg : Real.log M.gamma < 0 := Real.log_neg hgpos hgamma1
  have habs : |Real.log M.gamma| = -Real.log M.gamma := abs_of_neg hlogneg
  set u : ℝ := |Real.log M.gamma| with hu
  have hu1 : (1 : ℝ) ≤ u := by linarith only [hlog]
  have hlog3 : (0 : ℝ) < Real.log 3 - 1 := by linarith only [one_lt_log_three]
  /- the `s`-power is `u^{9/2}`, and it is at most `u^5` -/
  have hspow : homS M ^ (-(9 / 2) : ℝ) = u ^ (9 / 2 : ℝ) := by
    have hs : homS M = u⁻¹ := by rw [hu]; rfl
    rw [hs, Real.inv_rpow hlog0.le, Real.rpow_neg hlog0.le, inv_inv]
  have hupow : u ^ (9 / 2 : ℝ) ≤ u ^ (5 : ℕ) := by
    have h5 : u ^ (5 : ℕ) = u ^ (((5 : ℕ) : ℝ)) := (Real.rpow_natCast u 5).symm
    rw [h5]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  /- the mesoscale gap: `(n-m)/2 = -k/2 ≤ -5u` -/
  have hgapexp : ((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2 ≤ -(5 * u) := by
    have hk : 10 * u ≤ (homK M : ℝ) := homK_ge M
    have hn : ((m : ℝ) - ((homN M m : ℤ) : ℝ)) = (homK M : ℝ) := homN_gap M m
    linarith only [hk, hn]
  have hgapbound : (3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2) ≤
      (3 : ℝ) ^ (-(5 * u)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hgapexp
  /- `3^{-5u} = exp(-5 u log 3)` and `γ^5 = exp(-5u)` -/
  have hthree : (3 : ℝ) ^ (-(5 * u)) = Real.exp (-(5 * u * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hgam : M.gamma ^ (5 : ℕ) = Real.exp (-(5 * u)) := by
    have hexp : Real.exp (Real.log M.gamma) = M.gamma := Real.exp_log hgpos
    rw [← hexp, ← Real.exp_nat_mul]
    congr 1
    rw [habs]
    ring
  /- the sla -/
  have hkey : u ^ (5 : ℕ) * Real.exp (-(5 * u * Real.log 3)) ≤
      homGapConst * Real.exp (-(5 * u)) := by
    set a : ℝ := 5 * (Real.log 3 - 1) with ha
    have hapos : 0 < a := by rw [ha]; linarith only [hlog3]
    have hupos : (0 : ℝ) < u := by linarith only [hu1]
    have hfive := pow_five_le_exp (t := a * u) (mul_nonneg hapos.le hupos.le)
    have hmul : u ^ (5 : ℕ) ≤ 3125 / a ^ (5 : ℕ) * Real.exp (a * u) := by
      have hexp : (a * u) ^ (5 : ℕ) = a ^ (5 : ℕ) * u ^ (5 : ℕ) := by rw [mul_pow]
      rw [hexp] at hfive
      have hapow : (0 : ℝ) < a ^ (5 : ℕ) := pow_pos hapos 5
      rw [div_mul_eq_mul_div, le_div_iff₀ hapow]
      linarith only [hfive]
    have hconst : (3125 : ℝ) / a ^ (5 : ℕ) = homGapConst := by
      have ha5 : a ^ (5 : ℕ) = 3125 * (Real.log 3 - 1) ^ (5 : ℕ) := by
        rw [ha, mul_pow]; norm_num
      have hbne : ((Real.log 3 - 1) : ℝ) ^ (5 : ℕ) ≠ 0 := ne_of_gt (pow_pos hlog3 5)
      rw [homGapConst, inv_pow, ha5]
      field_simp
    have hsplit : Real.exp (a * u) * Real.exp (-(5 * u * Real.log 3)) =
        Real.exp (-(5 * u)) := by
      rw [← Real.exp_add]
      congr 1
      rw [ha]
      ring
    have hposE : (0 : ℝ) < Real.exp (-(5 * u * Real.log 3)) := Real.exp_pos _
    calc u ^ (5 : ℕ) * Real.exp (-(5 * u * Real.log 3))
        ≤ (3125 / a ^ (5 : ℕ) * Real.exp (a * u)) *
            Real.exp (-(5 * u * Real.log 3)) :=
          mul_le_mul_of_nonneg_right hmul hposE.le
      _ = (3125 / a ^ (5 : ℕ)) *
            (Real.exp (a * u) * Real.exp (-(5 * u * Real.log 3))) := by ring
      _ = homGapConst * Real.exp (-(5 * u)) := by rw [hconst, hsplit]
  rw [hspow, hgam]
  have hunn : (0 : ℝ) ≤ u ^ (9 / 2 : ℝ) := Real.rpow_nonneg (by linarith only [hu1]) _
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  calc u ^ (9 / 2 : ℝ) *
        (3 : ℝ) ^ (((((homN M m : ℤ) : ℝ)) - (m : ℝ)) / 2)
      ≤ u ^ (9 / 2 : ℝ) * (3 : ℝ) ^ (-(5 * u)) :=
        mul_le_mul_of_nonneg_left hgapbound hunn
    _ = u ^ (9 / 2 : ℝ) * Real.exp (-(5 * u * Real.log 3)) := by rw [hthree]
    _ ≤ u ^ (5 : ℕ) * Real.exp (-(5 * u * Real.log 3)) :=
        mul_le_mul_of_nonneg_right hupow (Real.exp_pos _).le
    _ ≤ homGapConst * Real.exp (-(5 * u)) := hkey

/-! ## 5. Step 3b: the weak gradient bound -/

/-- **Step 3b — the weak gradient bound.**

Substituting the gap absorption into Step 3a's second term, dividing by `σ̄_m`
(the node's "silent but arithmetically exact" division) and comparing with the
two summands of `EthmB(m)` — supplied here as the two hypotheses `hD1`, `hD2`,
which is exactly the manuscript's "comparing to the definition of `EthmB(m)`" —
gives

```
  3^{-ms} ‖∇u - ∇v‖_{W̲^{-s,∞}(□_m)} ≤ C D ( σ̄_m^{-1} 3^{m/2} + 3^{m/2} ).
```

`D` is the defect slot; `hD1` and `hD2` are the two `EthmB` comparisons, and
`ethmB_ge_first_summand` / the `ethmB_ge_gap` certify that the `EthmB` carrier
really dominates both.  `C = max(C_cg C_meso C_r, 4 C_cg K_g C_gap0)` is
displayed. -/
theorem stepThreeWeakGradientBound {C sigma D E1 Eq E2 Xfac s Xgap Kgap L : ℝ}
    (hC : 0 ≤ C) (hsigma : 0 < sigma) (hD : 0 ≤ D) (m : ℤ)
    (hD1 : s⁻¹ * Xfac * E1 * (1 + Eq) ≤ D)
    (hD2 : Kgap * Xgap * (1 + E2 ^ (2 : ℕ)) ≤ D)
    (hpre : sigma * L ≤ C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2)) +
        C * Kgap * Xgap * (1 + E2 ^ (2 : ℕ)) * (3 : ℝ) ^ ((m : ℝ) / 2)) :
    L ≤ 2 * C * D * (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2)) := by
  have hm : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hinv : sigma⁻¹ * sigma = 1 := inv_mul_cancel₀ (ne_of_gt hsigma)
  have hinvnn : (0 : ℝ) ≤ sigma⁻¹ := (inv_pos.mpr hsigma).le
  have hP : (0 : ℝ) ≤ sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) := mul_nonneg hinvnn hm
    linarith only [h1, hm]
  have hCD : (0 : ℝ) ≤ C * D := mul_nonneg hC hD
  /- divide the Step-3a display by `σ̄_m` -/
  have hdiv : sigma⁻¹ * (sigma * L) ≤
      sigma⁻¹ * (C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2)) +
        C * Kgap * Xgap * (1 + E2 ^ (2 : ℕ)) * (3 : ℝ) ^ ((m : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hpre hinvnn
  have hLeq : sigma⁻¹ * (sigma * L) = L := by
    rw [← mul_assoc, hinv, one_mul]
  /- the first summand, after division, is `C · G · (σ̄^{-1}3^{m/2} + 3^{m/2})` -/
  have hAeq : sigma⁻¹ * (C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2))) =
      C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
        (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2)) := by
    have hexp : sigma⁻¹ * (C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2))) =
        C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
          (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) +
            (sigma⁻¹ * sigma) * (3 : ℝ) ^ ((m : ℝ) / 2)) := by ring
    rw [hexp, hinv, one_mul]
  have hAle : C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
      (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2)) ≤
      C * D * (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 hC) hP
  /- the second summand, after divisi -/
  have hBeq : sigma⁻¹ * (C * Kgap * Xgap * (1 + E2 ^ (2 : ℕ)) * (3 : ℝ) ^ ((m : ℝ) / 2)) =
      C * (Kgap * Xgap * (1 + E2 ^ (2 : ℕ))) * (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2)) := by
    ring
  have hBle : C * (Kgap * Xgap * (1 + E2 ^ (2 : ℕ))) *
      (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2)) ≤
      C * D * (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2)) := by
    have hstep : C * (Kgap * Xgap * (1 + E2 ^ (2 : ℕ))) *
        (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2)) ≤
        C * D * (sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2 hC)
        (mul_nonneg hinvnn hm)
    refine hstep.trans ?_
    have hgrow : sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) ≤
        sigma⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) + (3 : ℝ) ^ ((m : ℝ) / 2) := by
      linarith only [hm]
    exact mul_le_mul_of_nonneg_left hgrow hCD
  have hsplit : sigma⁻¹ * (C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2)) +
        C * Kgap * Xgap * (1 + E2 ^ (2 : ℕ)) * (3 : ℝ) ^ ((m : ℝ) / 2)) =
      sigma⁻¹ * (C * (s⁻¹ * Xfac * E1 * (1 + Eq)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) + sigma * (3 : ℝ) ^ ((m : ℝ) / 2))) +
        sigma⁻¹ * (C * Kgap * Xgap * (1 + E2 ^ (2 : ℕ)) * (3 : ℝ) ^ ((m : ℝ) / 2)) := by
    ring
  rw [hLeq, hsplit, hAeq, hBeq] at hdiv
  have hfinal := hdiv.trans (add_le_add hAle hBle)
  linarith only [hfinal]

/-! ## 6. The `EthmB` comparison, machine-visible -/

/-- The FIRST summand of `EthmB(m)` is below `EthmB(m)` — the half of "comparing
to the definition of `EthmB(m)`" that Step 1 did not need.  Together
with the `ethmB_ge_gap` (the `C γ^5` summand) this certifies that the
two defect slots `hD1`, `hD2` of `stepThreeWeakGradientBound` are really
dominated by the `EthmB` carrier. -/
theorem ethmB_ge_first_summand (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) :
    ENNReal.ofReal ((s : ℝ)⁻¹) *
        (Y omega *
          (Support.fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
            (1 + Support.fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega))) ≤
      ethmB M Cgap Y m n s omega := by
  rw [ethmB_eq]
  exact le_self_add

end

end Algsuperdiff.Section4.Provider.Homogenization
