/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.G2RatioTail

/-!
# The explicit `ε`-threshold of the `𝒢₂` proportion lane

ABK26, §4.1, the constant-selection sentence `e.K.and.p.choices` read as a
condition on `ε` rather than as a choice of `K₂`.

The proved lane endpoints (`G2RatioTail.exists_ratioTail_eventG2_of_range` and
its shifted twin) deliver the tail *from a threshold on*: they produce, after
`(r, M, s, θ, c₁)`, some `ε₀ > 0` and assert the tail for every `ε ≥ ε₀`.  The
threshold is not an artefact — `Support.eventG2` grows with `ε`, so the
small-`ε` side is genuinely the hard one — but the existential hides which
condition on the parameters actually makes it hold.  This module names it.

## Contents

* `g2MomentExponent` — the lane's moment exponent `p`, in closed form
  (`max{1, 4/s, 64rΛ/(sθ)}`, `Λ = log(3r) + c₁r`), chosen after `c₁`;
* `g2Normalizer` — the lane's Appendix-D normalizer `D`, in closed form: the
  two Step-2 Orlicz scales at the closed `s`-power evaluations of `G2Arith` and
  the two per-cube amplitudes of the Section 3 anchor;
* `g2Threshold d r s θ c₁ = 36(1+C⋆)·D/θ` — the **explicit `ε²`-threshold**.
  The proved lane's own `ε₀` is `√(g2Threshold …)`; the squared form is the
  honest one, since the condition the proof consumes is `36(1+C⋆)D ≤ θε²`, and
  it keeps `Real.sqrt` out of the statement entirely;
* `g2Threshold_le_of` — a **sufficient parameter condition** for
  `g2Threshold … ≤ ε²`, in two explicit clauses;
* `g2Threshold_le_of_gammaPow` — the second clause in `γ`-power form.

## The two clauses

Writing `κ₁(d)`, `κ₂(d)` for `g2ThresholdConstOne`, `g2ThresholdConstTwo`:

```
(1)   κ₁(d) r² (1+c₁) C² γ              ≤ θ² c⋆² s⁵ ε²
(2)   κ₂(d) r⁸ (1+c₁)⁴ exp(−2c⋆³/(Cγ))  ≤ θ⁵ s⁹ ε²
```

Clause (1) is the `𝒢₂` twin of the `𝒢₁` lane's honest condition
`K(d,r)(1+c₁)γ ≤ θ c⋆ s⁶ ε²` (`G1ThresholdArith.g1Majorant_le_shellThreshold`);
it is the binding one.  Clause (2) carries the `θ^{-4}` of the fourth moment but
is multiplied by the exponentially small second Step-2 amplitude, so it costs
nothing at small `γ`: `g2Threshold_le_of_gammaPow` trades it for
`(315/8)κ₂(d) r⁸(1+c₁)⁴ C⁷ γ⁷ ≤ θ⁵ c⋆²¹ s⁹ ε²`.

## Scope

Provider material: proved local helpers.  Every transcendental step is an
abstract-real private helper.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`, in particular the
  constant-selection sentence.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums
open Algsuperdiff.Section4.Probability.ScalesConcentration

noncomputable section

variable {d : ℕ}

/-! ## 1. Abstract-real helpers -/

private theorem div_le_div_right_of_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)

/-- `log(3r) ≤ 3r − 1`: the only place the logarithm of the rate is opened. -/
private theorem log_three_mul_le {r : ℝ} (hr : 1 ≤ r) : Real.log (3 * r) ≤ 3 * r - 1 :=
  Real.log_le_sub_one_of_pos (by linarith only [hr])

/-- `exp(−x)² = exp(−2x)`: the only place the second amplitude's exponential is
squared. -/
private theorem exp_neg_sq (x : ℝ) : Real.exp (-x) ^ (2 : ℕ) = Real.exp (-(2 * x)) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- `x^(4:ℝ) = x^(4:ℕ)`: the only place the fourth-moment `rpow` is opened. -/
private theorem rpow_four (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The exponentially small amplitude against a seventh power of `γ`.**
`exp(−w) ≤ 5040/w⁷` at `w = 2u³/(xy)`, in the form the second threshold clause
consumes.  This is the only place the second amplitude's exponential is
estimated. -/
private theorem exp_neg_two_cube_le {x u y : ℝ} (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    Real.exp (-(2 * (x⁻¹ * u ^ (3 : ℕ) * y⁻¹)))
      ≤ 315 / 8 * (x ^ (7 : ℕ) * y ^ (7 : ℕ)) / u ^ (21 : ℕ) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hune : u ≠ 0 := ne_of_gt hu
  have hyne : y ≠ 0 := ne_of_gt hy
  have hw0 : (0 : ℝ) < 2 * (x⁻¹ * u ^ (3 : ℕ) * y⁻¹) := by
    have h := mul_pos (mul_pos (inv_pos.2 hx) (pow_pos hu 3)) (inv_pos.2 hy)
    linarith only [h]
  have hexp := exp_neg_le_seven hw0
  have hpow : (2 * (x⁻¹ * u ^ (3 : ℕ) * y⁻¹)) ^ (7 : ℕ)
      = 128 * u ^ (21 : ℕ) / (x ^ (7 : ℕ) * y ^ (7 : ℕ)) := by
    field_simp
    ring
  rw [hpow] at hexp
  refine le_trans hexp (le_of_eq ?_)
  field_simp
  ring

/-! ## 2. The three closed-form lane parameters -/

/-- **The `𝒢₂` lane's moment exponent, in closed form.**  This is the `p` the
proved endpoint constructs inside its existential: `max{1, 4/s, 64rΛ/(sθ)}`
with `Λ = log(3r) + c₁r`.  It is chosen *after* the rate `c₁`, which is why the
lane carries no rate ceiling. -/
def g2MomentExponent (r : ℕ) (s theta c1 : ℝ) : ℝ :=
  max 1 (max (4 / s) (64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) / (s * theta)))

/-- **The `𝒢₂` lane's Appendix-D normalizer, in closed form.**  This is the `D` the
proved endpoint constructs inside its existential: the two Step-2 Orlicz scales
at the closed `s`-power evaluations `xcalNormOne d · s^{−2}` and
`xcalNormQuarter d · s^{−5}` of `G2Arith`, at the two per-cube amplitudes
`cubeAmpOne`, `cubeAmpTwo` of the Section 3 anchor. -/
def g2Normalizer (d r : ℕ) (C : ℝ) (M : ABKModel d) (s theta c1 : ℝ) : ℝ :=
  gammaMomentConst 1 * g2MomentExponent r s theta c1 *
      (gammaTriangleConst (1 : ℝ) *
        (xcalNormOne d / s ^ (2 : ℕ) * (2 * cubeAmpOne d C M s ^ (2 : ℕ)))) +
    gammaMomentConst (1 / 4) * g2MomentExponent r s theta c1 ^ (4 : ℝ) *
      (gammaTriangleConst (1 / 4 : ℝ) *
        (xcalNormQuarter d / s ^ (5 : ℕ) * (2 * cubeAmpTwo d C M ^ (2 : ℕ))))

/-- **The explicit `ε²`-threshold of the `𝒢₂` proportion lane.**

`g2Threshold d r s θ c₁ = 36(1+C⋆)·D/θ`, with `D = g2Normalizer …`.  The proved
lane endpoint's own threshold is `ε₀ = √(g2Threshold …)`; the condition its
proof actually consumes is `g2Threshold … ≤ ε²`, which is why the squared form
is the honest one to name.  No existential and no choice enters: `C` is the
dimensional constant of the two-term per-cube display and everything else is a
parameter of the lane. -/
def g2Threshold (d r : ℕ) (C : ℝ) (M : ABKModel d) (s theta c1 : ℝ) : ℝ :=
  36 * (1 + Cstar) * g2Normalizer d r C M s theta c1 / theta

/-! ## 3. Positivity -/

theorem one_le_g2MomentExponent (r : ℕ) (s theta c1 : ℝ) :
    1 ≤ g2MomentExponent r s theta c1 := le_max_left _ _

theorem g2MomentExponent_pos (r : ℕ) (s theta c1 : ℝ) :
    0 < g2MomentExponent r s theta c1 :=
  lt_of_lt_of_le zero_lt_one (one_le_g2MomentExponent r s theta c1)

theorem four_div_le_g2MomentExponent (r : ℕ) (s theta c1 : ℝ) :
    4 / s ≤ g2MomentExponent r s theta c1 :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem rate_le_g2MomentExponent (r : ℕ) (s theta c1 : ℝ) :
    64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ)) / (s * theta)
      ≤ g2MomentExponent r s theta c1 :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- Positivity of the `Γ₂`-lane per-cube amplitude.  (The proved lanes keep their
own copies private, so this one is re-derived rather than reused.) -/
theorem cubeAmpOne_pos_of {C : ℝ} (hC : 0 < C) (M : ABKModel d) {s : ℝ} (hs : 0 < s) :
    0 < cubeAmpOne d C M s := by
  have hpen : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 M.shellPrefix.gamma_pos
  rw [cubeAmpOne]
  exact mul_pos h3 (mul_pos hpen
    (mul_pos (mul_pos (mul_pos hC (inv_pos.2 hcs)) (inv_pos.2 hs)) hg))

/-- Positivity of the `Γ_{1/2}`-lane per-cube amplitude. -/
theorem cubeAmpTwo_pos_of (C : ℝ) (M : ABKModel d) : 0 < cubeAmpTwo d C M := by
  have hpen : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [cubeAmpTwo]
  exact mul_pos h3 (mul_pos hpen (Real.exp_pos _))

theorem g2Normalizer_pos {C s : ℝ} (hC : 0 < C) (M : ABKModel d) (r : ℕ) (hs : 0 < s)
    (theta c1 : ℝ) : 0 < g2Normalizer d r C M s theta c1 := by
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hgtc1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hgtc4 : (0 : ℝ) < gammaTriangleConst (1 / 4 : ℝ) := gammaTriangleConst_pos
  have hp0 : (0 : ℝ) < g2MomentExponent r s theta c1 := g2MomentExponent_pos r s theta c1
  have hprpow : (0 : ℝ) < g2MomentExponent r s theta c1 ^ (4 : ℝ) :=
    Real.rpow_pos_of_pos hp0 _
  have hA1 : 0 < cubeAmpOne d C M s := cubeAmpOne_pos_of hC M hs
  have hA2 : 0 < cubeAmpTwo d C M := cubeAmpTwo_pos_of C M
  rw [g2Normalizer]
  refine add_pos (mul_pos (mul_pos hgmc1 hp0) (mul_pos hgtc1 ?_))
    (mul_pos (mul_pos hgmc4 hprpow) (mul_pos hgtc4 ?_))
  · exact mul_pos (div_pos (xcalNormOne_pos d) (pow_pos hs 2))
      (mul_pos two_pos (pow_pos hA1 2))
  · exact mul_pos (div_pos (xcalNormQuarter_pos d) (pow_pos hs 5))
      (mul_pos two_pos (pow_pos hA2 2))

theorem g2Threshold_pos {C s theta : ℝ} (hC : 0 < C) (M : ABKModel d) (r : ℕ) (hs : 0 < s)
    (htheta : 0 < theta) (c1 : ℝ) : 0 < g2Threshold d r C M s theta c1 := by
  have hCs : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  rw [g2Threshold]
  exact div_pos (mul_pos (by linarith only [hCs]) (g2Normalizer_pos hC M r hs theta c1)) htheta

/-! ## 4. The closed majorant of the moment exponent -/

/-- **The moment exponent is at most `192 r²(1+c₁)/(sθ)`.**  All three branches of
the `max` are paid by that single monomial: the constant branch by `sθ ≤ 1`, the
`4/s` branch by `θ ≤ 1`, and the rate branch by `log(3r) ≤ 3r − 1`. -/
theorem g2MomentExponent_le {r : ℕ} {s theta c1 : ℝ} (hr1 : 1 ≤ r) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1) :
    g2MomentExponent r s theta c1 ≤ 192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta) := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hst0 : (0 : ℝ) < s * theta := mul_pos hs0 hth0
  have hst1 : s * theta ≤ 1 := by
    have h := mul_le_mul hs1 hth1 hth0.le zero_le_one
    linarith only [h]
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ (2 : ℕ) := one_le_pow₀ hrR
  have hc1' : (1 : ℝ) ≤ 1 + c1 := by linarith only [hc1]
  have hbig : (192 : ℝ) ≤ 192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) := by
    have h := mul_le_mul hr2 hc1' (by norm_num) (by linarith only [hr2])
    linarith only [h]
  refine max_le ?_ (max_le ?_ ?_)
  · rw [le_div_iff₀ hst0]
    linarith only [hst1, hbig]
  · rw [div_le_div_iff₀ hs0 hst0]
    have hts : s * theta ≤ s := by
      have h := mul_le_mul_of_nonneg_left hth1 hs0.le
      linarith only [h]
    have hmul := mul_le_mul_of_nonneg_right hbig hs0.le
    linarith only [hts, hmul, hs0]
  · refine div_le_div_right_of_le ?_ hst0.le
    have hlog := log_three_mul_le hrR
    have h1 : Real.log (3 * (r : ℝ)) + c1 * (r : ℝ) ≤ 3 * (r : ℝ) + c1 * (r : ℝ) := by
      linarith only [hlog]
    have h2 : 64 * (r : ℝ) * (Real.log (3 * (r : ℝ)) + c1 * (r : ℝ))
        ≤ 64 * (r : ℝ) * (3 * (r : ℝ) + c1 * (r : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith only [hrR])
    have h3 : (0 : ℝ) ≤ 128 * c1 * (r : ℝ) ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (by norm_num) hc1) (by positivity)
    linarith only [h2, h3]

/-- The fourth power of the majorant of the moment exponent, expanded. -/
theorem g2MomentExponent_rpow_four_le {r : ℕ} {s theta c1 : ℝ} (hr1 : 1 ≤ r) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1) :
    g2MomentExponent r s theta c1 ^ (4 : ℝ)
      ≤ 1358954496 * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
          / (s ^ (4 : ℕ) * theta ^ (4 : ℕ)) := by
  have hple := g2MomentExponent_le hr1 hs0 hs1 hth0 hth1 hc1
  have hp0 : (0 : ℝ) < g2MomentExponent r s theta c1 := g2MomentExponent_pos r s theta c1
  have hpow : g2MomentExponent r s theta c1 ^ (4 : ℕ)
      ≤ (192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hp0.le hple 4
  have hexpand : (192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta)) ^ (4 : ℕ)
      = 1358954496 * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
          / (s ^ (4 : ℕ) * theta ^ (4 : ℕ)) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, ← pow_mul]
    norm_num
  rw [rpow_four, ← hexpand]
  exact hpow

/-! ## 5. The two squared amplitudes -/

private theorem cubeAmpOne_sq (C : ℝ) (M : ABKModel d) (s : ℝ) :
    cubeAmpOne d C M s ^ (2 : ℕ)
      = 3 * annulusPenalty d 2 1 ^ (2 : ℕ) * C ^ (2 : ℕ) * M.gamma
          / (Disorder.cstar M ^ (2 : ℕ) * s ^ (2 : ℕ)) := by
  have h3 : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have hG : Real.sqrt M.gamma ^ (2 : ℕ) = M.gamma := Real.sq_sqrt M.shellPrefix.gamma_pos.le
  have hexpand : cubeAmpOne d C M s ^ (2 : ℕ)
      = Real.sqrt 3 ^ (2 : ℕ) * annulusPenalty d 2 1 ^ (2 : ℕ) * C ^ (2 : ℕ)
        * ((Disorder.cstar M)⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (2 : ℕ)
        * Real.sqrt M.gamma ^ (2 : ℕ) := by
    rw [cubeAmpOne]; ring
  rw [hexpand, h3, hG]
  ring

private theorem cubeAmpTwo_sq (C : ℝ) (M : ABKModel d) :
    cubeAmpTwo d C M ^ (2 : ℕ)
      = 3 * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)
          * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) := by
  have h3 : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have hexpand : cubeAmpTwo d C M ^ (2 : ℕ)
      = Real.sqrt 3 ^ (2 : ℕ) * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)
        * Real.exp (-(C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹)) ^ (2 : ℕ) := by
    rw [cubeAmpTwo]; ring
  rw [hexpand, h3, exp_neg_sq]

/-! ## 6. The two threshold constants -/

/-- The `d`-only constant of the binding (`Γ₂`-lane) clause of the `𝒢₂`
threshold condition. -/
def g2ThresholdConstOne (d : ℕ) : ℝ :=
  82944 * (1 + Cstar) * gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
    * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)

/-- The `d`-only constant of the exponentially small (`Γ_{1/2}`-lane) clause of
the `𝒢₂` threshold condition. -/
def g2ThresholdConstTwo (d : ℕ) : ℝ :=
  587068342272 * (1 + Cstar) * gammaMomentConst (1 / 4) * gammaTriangleConst (1 / 4 : ℝ)
    * xcalNormQuarter d * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)

theorem g2ThresholdConstOne_pos (d : ℕ) : 0 < g2ThresholdConstOne d := by
  have hCs : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgtc1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hpen : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  rw [g2ThresholdConstOne]
  exact mul_pos (mul_pos (mul_pos (mul_pos (by linarith only [hCs]) hgmc1) hgtc1)
    (xcalNormOne_pos d)) (pow_pos hpen 2)

theorem g2ThresholdConstTwo_pos (d : ℕ) : 0 < g2ThresholdConstTwo d := by
  have hCs : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hgtc4 : (0 : ℝ) < gammaTriangleConst (1 / 4 : ℝ) := gammaTriangleConst_pos
  have hpen : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  rw [g2ThresholdConstTwo]
  exact mul_pos (mul_pos (mul_pos (mul_pos (by linarith only [hCs]) hgmc4) hgtc4)
    (xcalNormQuarter_pos d)) (pow_pos hpen 2)

/-! ## 7. The sufficient parameter condition -/

/-- **The explicit `ε`-threshold is met under two closed parameter conditions.**

```
(1)   κ₁(d) r² (1+c₁) C² γ              ≤ θ² c⋆² s⁵ ε²
(2)   κ₂(d) r⁸ (1+c₁)⁴ exp(−2c⋆³/(Cγ))  ≤ θ⁵ s⁹ ε²
```

Clause (1) is the binding one and is the `𝒢₂` twin of the `𝒢₁` lane's honest
condition; clause (2) carries the fourth moment's `θ^{-4}` against the
exponentially small second Step-2 amplitude and costs nothing at small `γ` (see
`g2Threshold_le_of_gammaPow`).  Both are *sufficient*; no converse is claimed
here.  The `ε²` on the right of both clauses is why the condition cannot be
removed by enlarging a constant: it is a genuine restriction on `ε` from
below. -/
theorem g2Threshold_le_of (M : ABKModel d) {C s theta c1 ep : ℝ} {r : ℕ}
    (hr1 : 1 ≤ r) (hC0 : 0 < C) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1)
    (hcond1 : g2ThresholdConstOne d * (r : ℝ) ^ (2 : ℕ) * (1 + c1) * C ^ (2 : ℕ) * M.gamma
      ≤ theta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ))
    (hcond2 : g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
        * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹)))
      ≤ theta ^ (5 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ)) :
    g2Threshold d r C M s theta c1 ≤ ep ^ (2 : ℕ) := by
  have hCs : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hG0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgmc1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hgmc4 : (0 : ℝ) < gammaMomentConst (1 / 4) := gammaMomentConst_pos (by norm_num)
  have hgtc1 : (0 : ℝ) < gammaTriangleConst (1 : ℝ) := gammaTriangleConst_pos
  have hgtc4 : (0 : ℝ) < gammaTriangleConst (1 / 4 : ℝ) := gammaTriangleConst_pos
  have hpen1 : (0 : ℝ) < annulusPenalty d 2 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have hpen2 : (0 : ℝ) < annulusPenalty d (1 / 2) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_annulusPenalty d (by norm_num) 1)
  have hE0 : (0 : ℝ) < Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) :=
    Real.exp_pos _
  -- the first (binding) term
  have hT1 : 36 * (1 + Cstar) *
      (gammaMomentConst 1 * g2MomentExponent r s theta c1 *
        (gammaTriangleConst (1 : ℝ) *
          (xcalNormOne d / s ^ (2 : ℕ) * (2 * cubeAmpOne d C M s ^ (2 : ℕ)))))
      ≤ theta * ep ^ (2 : ℕ) / 2 := by
    have hfac : (0 : ℝ) ≤ 216 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
        * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * C ^ (2 : ℕ) * M.gamma
          / (Disorder.cstar M ^ (2 : ℕ) * s ^ (4 : ℕ)) := by
      refine div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hCs])
        (le_of_lt (mul_pos (mul_pos (mul_pos hgmc1 hgtc1) (xcalNormOne_pos d))
          (pow_pos hpen1 2)))) (le_of_lt (pow_pos hC0 2))) hG0.le)
        (le_of_lt (mul_pos (pow_pos hcs0 2) (pow_pos hs0 4)))
    have hden : (0 : ℝ) < Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * theta :=
      mul_pos (mul_pos (pow_pos hcs0 2) (pow_pos hs0 5)) hth0
    calc 36 * (1 + Cstar) *
          (gammaMomentConst 1 * g2MomentExponent r s theta c1 *
            (gammaTriangleConst (1 : ℝ) *
              (xcalNormOne d / s ^ (2 : ℕ) * (2 * cubeAmpOne d C M s ^ (2 : ℕ)))))
        = 216 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
            * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * C ^ (2 : ℕ) * M.gamma
              / (Disorder.cstar M ^ (2 : ℕ) * s ^ (4 : ℕ))
            * g2MomentExponent r s theta c1 := by
          rw [cubeAmpOne_sq]; ring
      _ ≤ 216 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
            * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * C ^ (2 : ℕ) * M.gamma
              / (Disorder.cstar M ^ (2 : ℕ) * s ^ (4 : ℕ))
            * (192 * (r : ℝ) ^ (2 : ℕ) * (1 + c1) / (s * theta)) :=
          mul_le_mul_of_nonneg_left (g2MomentExponent_le hr1 hs0 hs1 hth0 hth1 hc1) hfac
      _ = 41472 * (1 + Cstar) * (gammaMomentConst 1 * gammaTriangleConst (1 : ℝ)
            * xcalNormOne d * annulusPenalty d 2 1 ^ (2 : ℕ)) * (r : ℝ) ^ (2 : ℕ) * (1 + c1)
            * C ^ (2 : ℕ) * M.gamma
            / (Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * theta) := by
          ring
      _ ≤ theta * ep ^ (2 : ℕ) / 2 := by
          rw [div_le_iff₀ hden]
          rw [g2ThresholdConstOne] at hcond1
          linarith only [hcond1]
  -- the second (exponentially small) term
  have hT2 : 36 * (1 + Cstar) *
      (gammaMomentConst (1 / 4) * g2MomentExponent r s theta c1 ^ (4 : ℝ) *
        (gammaTriangleConst (1 / 4 : ℝ) *
          (xcalNormQuarter d / s ^ (5 : ℕ) * (2 * cubeAmpTwo d C M ^ (2 : ℕ)))))
      ≤ theta * ep ^ (2 : ℕ) / 2 := by
    have hfac : (0 : ℝ) ≤ 216 * (1 + Cstar) * (gammaMomentConst (1 / 4)
        * gammaTriangleConst (1 / 4 : ℝ) * xcalNormQuarter d
        * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ))
        * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) / s ^ (5 : ℕ) := by
      refine div_nonneg (mul_nonneg (mul_nonneg (by linarith only [hCs])
        (le_of_lt (mul_pos (mul_pos (mul_pos hgmc4 hgtc4) (xcalNormQuarter_pos d))
          (pow_pos hpen2 2)))) hE0.le) (le_of_lt (pow_pos hs0 5))
    have hden : (0 : ℝ) < s ^ (9 : ℕ) * theta ^ (4 : ℕ) :=
      mul_pos (pow_pos hs0 9) (pow_pos hth0 4)
    calc 36 * (1 + Cstar) *
          (gammaMomentConst (1 / 4) * g2MomentExponent r s theta c1 ^ (4 : ℝ) *
            (gammaTriangleConst (1 / 4 : ℝ) *
              (xcalNormQuarter d / s ^ (5 : ℕ) * (2 * cubeAmpTwo d C M ^ (2 : ℕ)))))
        = 216 * (1 + Cstar) * (gammaMomentConst (1 / 4) * gammaTriangleConst (1 / 4 : ℝ)
            * xcalNormQuarter d * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ))
            * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) / s ^ (5 : ℕ)
            * g2MomentExponent r s theta c1 ^ (4 : ℝ) := by
          rw [cubeAmpTwo_sq]; ring
      _ ≤ 216 * (1 + Cstar) * (gammaMomentConst (1 / 4) * gammaTriangleConst (1 / 4 : ℝ)
            * xcalNormQuarter d * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ))
            * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹))) / s ^ (5 : ℕ)
            * (1358954496 * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
                / (s ^ (4 : ℕ) * theta ^ (4 : ℕ))) :=
          mul_le_mul_of_nonneg_left
            (g2MomentExponent_rpow_four_le hr1 hs0 hs1 hth0 hth1 hc1) hfac
      _ = 293534171136 * (1 + Cstar) * (gammaMomentConst (1 / 4)
            * gammaTriangleConst (1 / 4 : ℝ) * xcalNormQuarter d
            * annulusPenalty d (1 / 2) 1 ^ (2 : ℕ)) * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
            * Real.exp (-(2 * (C⁻¹ * Disorder.cstar M ^ (3 : ℕ) * M.gamma⁻¹)))
            / (s ^ (9 : ℕ) * theta ^ (4 : ℕ)) := by
          ring
      _ ≤ theta * ep ^ (2 : ℕ) / 2 := by
          rw [div_le_iff₀ hden]
          rw [g2ThresholdConstTwo] at hcond2
          linarith only [hcond2]
  rw [g2Threshold, div_le_iff₀ hth0, g2Normalizer]
  linarith only [hT1, hT2]

/-- **The second clause in `γ`-power form.**  `exp(−w) ≤ 5040/w⁷` at
`w = 2c⋆³/(Cγ)` turns the exponentially small clause into

```
(2')  (315/8) κ₂(d) r⁸ (1+c₁)⁴ C⁷ γ⁷ ≤ θ⁵ c⋆²¹ s⁹ ε² ,
```

which makes visible that this clause is *not* the obstruction: it is six powers
of `γ` weaker than the binding clause (1), which is linear in `γ`. -/
theorem g2Threshold_le_of_gammaPow (M : ABKModel d) {C s theta c1 ep : ℝ} {r : ℕ}
    (hr1 : 1 ≤ r) (hC0 : 0 < C) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hth0 : 0 < theta) (hth1 : theta ≤ 1) (hc1 : 0 ≤ c1)
    (hcond1 : g2ThresholdConstOne d * (r : ℝ) ^ (2 : ℕ) * (1 + c1) * C ^ (2 : ℕ) * M.gamma
      ≤ theta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ))
    (hcond2 : 315 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
        * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ)
      ≤ theta ^ (5 : ℕ) * Disorder.cstar M ^ (21 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ)) :
    g2Threshold d r C M s theta c1 ≤ ep ^ (2 : ℕ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hG0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcspow : (0 : ℝ) < Disorder.cstar M ^ (21 : ℕ) := pow_pos hcs0 21
  have hexp := exp_neg_two_cube_le hC0 hcs0 hG0
  have hpre : (0 : ℝ) ≤ g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ) :=
    mul_nonneg (mul_nonneg (g2ThresholdConstTwo_pos d).le (pow_nonneg (Nat.cast_nonneg r) 8))
      (pow_nonneg (by linarith only [hc1]) 4)
  have hstep := mul_le_mul_of_nonneg_left hexp hpre
  have hfinal : 315 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
      * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ) / Disorder.cstar M ^ (21 : ℕ)
      ≤ theta ^ (5 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ) := by
    rw [div_le_iff₀ hcspow]
    linarith only [hcond2]
  refine g2Threshold_le_of M hr1 hC0 hs0 hs1 hth0 hth1 hc1 hcond1 (le_trans hstep ?_)
  calc g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
        * (315 / 8 * (C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ)) / Disorder.cstar M ^ (21 : ℕ))
      = 315 / 8 * g2ThresholdConstTwo d * (r : ℝ) ^ (8 : ℕ) * (1 + c1) ^ (4 : ℕ)
          * C ^ (7 : ℕ) * M.gamma ^ (7 : ℕ) / Disorder.cstar M ^ (21 : ℕ) := by ring
    _ ≤ theta ^ (5 : ℕ) * s ^ (9 : ℕ) * ep ^ (2 : ℕ) := hfinal

end

end Algsuperdiff.Section4.Provider.Proportion
