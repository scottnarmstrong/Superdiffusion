/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.G1RatioTail

/-!
# An explicit majorant for the `𝒢₁` proportion threshold

`G1RatioTail.exists_ratioTail_eventG1` delivers the `𝒢₁` proportion tail at an
existential, unexposed threshold `T₀`, and only at the dependence range `r = 1`.
This module replaces that existential by an **explicit closed form**, valid at
every `r ≥ 1`:

* `g1ThresholdConst d r` — a positive constant depending only on `d` and `r`
  (through `Cstar`, `gammaMomentConst`, `atomG1bScale` and `log 3`);
* `g1Majorant d r s θ c₁ = √(g1ThresholdConst d r (1+c₁) / (s⁴ θ))`;
* `ratioTail_eventG1_of_majorant` — the `exp(-c₁n)/3` tail at every
  `T ≥ g1Majorant d r s θ c₁`.

## The honest reading of the threshold condition

`g1Majorant_le_shellThreshold` certifies that this majorant sits below the
threshold `T = s ε √(c⋆) (√γ)⁻¹` at which the Section 4 support layer
instantiates `𝒢₁` inside `Support.goodEventBase`, under the explicit condition

```
K(d,r) (1 + c₁) γ ≤ θ c⋆ s⁶ ε²          (`hcond`)
```

which is exactly `T₀² ≤ (s ε)² c⋆ γ⁻¹` written out.  Measured against the
manuscript's printed side condition `e.theta.cond.two` (`T² ≥ C s^{-2}
max{s^{-1}, θ^{-1}}`), `hcond` is **one power of `s^{-2}` stronger**: the
printed condition would read `s⁴` where `hcond` needs `s⁶`.  Nothing in this
module consumes the printed condition, and no declaration here claims a source
node, or any fraction of one, closed.

## References

* ABK26, `l.ratio.of.good.scales.for.k`, Step 3.
* ABK26, `d.good.event.for.lambda`, (the `𝒢₁` threshold `s ε c⋆^{1/2}
  γ^{-1/2}`).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Abstract-real helpers

Every transcendental atom (`Real.exp`, `Real.log`, `Real.rpow`, `Real.sqrt`) is
confined to this section; the closed-form arithmetic below sees only opaque
reals. -/

/-- `x^{1/p} ≤ 1 + x` for `x ≥ 0` and `p ≥ 1`. -/
private theorem rpow_one_div_le_one_add {x p : ℝ} (hx : 0 ≤ x) (hp : 1 ≤ p) :
    x ^ (1 / p) ≤ 1 + x := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have he0 : (0 : ℝ) ≤ 1 / p := div_nonneg zero_le_one hp0.le
  have he1 : 1 / p ≤ 1 := by
    rw [div_le_iff₀ hp0]; linarith only [hp]
  rcases le_or_gt x 1 with h | h
  · have hle := Real.rpow_le_one hx h he0
    linarith only [hle, hx]
  · have hle := Real.rpow_le_rpow_of_exponent_le h.le he1
    rw [Real.rpow_one] at hle
    linarith only [hle]

/-- The purely algebraic core of `rpow_neg_inv_le_three`: if `0 ≤ L ≤ 1/x - 1`
and `1/q ≤ x`, then `L/q ≤ 1 - x ≤ 1`. -/
private theorem mul_one_div_le_one {L x q : ℝ} (hx0 : 0 < x) (hq0 : 0 < q)
    (hL0 : 0 ≤ L) (hLx : L ≤ 1 / x - 1) (hqx : 1 / q ≤ x) : L * (1 / q) ≤ 1 := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hb0 : (0 : ℝ) ≤ 1 / x - 1 := le_trans hL0 hLx
  have hstep : L * (1 / q) ≤ (1 / x - 1) * x :=
    mul_le_mul hLx hqx (div_nonneg zero_le_one hq0.le) hb0
  have hxx : (1 / x - 1) * x = 1 - x := by field_simp
  rw [hxx] at hstep
  linarith only [hstep, hx0]

/-- **The sharp negative-exponent bound.**  For `x ∈ (0,1]` and any `q ≥ 1/x`,
`x^{-1/q} ≤ 3`.  The point is that the exponent `(1/q)·log(1/x)` is at most
`x·(1/x − 1) = 1 − x ≤ 1`, so the whole power is at most `e < 3` — *not* the
crude `x^{-1/q} ≤ x⁻¹`, which would cost two extra powers of `θ⁻¹`. -/
private theorem rpow_neg_inv_le_three {x q : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hq : 1 / x ≤ q) : x ^ (-1 / q) ≤ 3 := by
  have hxq : (1 : ℝ) ≤ q * x := (div_le_iff₀ hx0).mp hq
  have hq0 : (0 : ℝ) < q := by
    rcases le_or_gt q 0 with h | h
    · exfalso
      have hle : q * x ≤ 0 * x := mul_le_mul_of_nonneg_right h hx0.le
      rw [zero_mul] at hle
      linarith only [hle, hxq]
    · exact h
  have hqx : 1 / q ≤ x := by
    rw [div_le_iff₀ hq0]; linarith only [hxq]
  have hL0 : (0 : ℝ) ≤ -Real.log x := by
    have h := Real.log_nonpos hx0.le hx1
    linarith only [h]
  have hLx : -Real.log x ≤ 1 / x - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos one_pos hx0)
    rw [one_div, Real.log_inv] at h
    rw [one_div]
    exact h
  have hexp : Real.log x * (-1 / q) ≤ 1 := by
    have h := mul_one_div_le_one hx0 hq0 hL0 hLx hqx
    have heq : Real.log x * (-1 / q) = -Real.log x * (1 / q) := by ring
    rw [heq]
    exact h
  rw [Real.rpow_def_of_pos hx0]
  calc Real.exp (Real.log x * (-1 / q)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hexp
    _ ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))

/-- `a ≤ √b` from `0 ≤ a` and `a² ≤ b`. -/
private theorem le_sqrt_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (h : a ^ (2 : ℕ) ≤ b) :
    a ≤ Real.sqrt b := by
  have h1 : Real.sqrt (a ^ (2 : ℕ)) ≤ Real.sqrt b := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha] at h1

/-- `a ≤ b` from `0 ≤ a`, `0 ≤ b` and `a² ≤ b²`. -/
private theorem le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) : a ≤ b := by
  have h1 : Real.sqrt (a ^ (2 : ℕ)) ≤ Real.sqrt (b ^ (2 : ℕ)) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at h1

/-- `3^{s/2} ≤ 2` for `s ≤ 1`. -/
private theorem three_rpow_half_le_two {s : ℝ} (hs1 : s ≤ 1) :
    (3 : ℝ) ^ (s / 2) ≤ 2 := by
  have h1 : (3 : ℝ) ^ (s / 2) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs1])
  have h2 : (3 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
  have h3 : Real.sqrt 3 ≤ 2 :=
    calc Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  calc (3 : ℝ) ^ (s / 2) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) := h1
    _ = Real.sqrt 3 := h2
    _ ≤ 2 := h3

/-- `g1bConst s = 3^{s/2}(12/s) ≤ 24/s` for `s ∈ (0,1]`. -/
private theorem g1bConst_le_of_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    g1bConst s ≤ 24 / s := by
  have h3 : (3 : ℝ) ^ (s / 2) ≤ 2 := three_rpow_half_le_two hs1
  have h12 : (0 : ℝ) ≤ 12 / s := div_nonneg (by norm_num) hs0.le
  calc g1bConst s = (3 : ℝ) ^ (s / 2) * (12 / s) := rfl
    _ ≤ 2 * (12 / s) := mul_le_mul_of_nonneg_right h3 h12
    _ = 24 / s := by ring

/-- `log(6r) + r ≥ 0` for every natural `r` (at `r = 0` both sides vanish). -/
private theorem logSixMul_nonneg (r : ℕ) : 0 ≤ Real.log (6 * (r : ℝ)) + (r : ℝ) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; norm_num
  · have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hlog := Real.log_nonneg (by linarith only [hrR] : (1 : ℝ) ≤ 6 * (r : ℝ))
    linarith only [hlog, hrR]

/-! ## 2. Purely algebraic helpers (no transcendental atoms) -/

/-- Monotonicity of `· / c`. -/
private theorem div_le_div_right_of_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h : b / c * c = b := by field_simp
  rw [div_le_iff₀ hc, h]
  exact hab

/-- Inserting the free `s^{-4}` (for `s ≤ 1`) while enlarging the numerator. -/
private theorem div_le_div_pow_four {a b s theta : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hth : 0 < theta) :
    a / theta ≤ b / (s ^ (4 : ℕ) * theta) := by
  have hs4 : (0 : ℝ) < s ^ (4 : ℕ) := pow_pos hs0 4
  have hs4le : s ^ (4 : ℕ) ≤ 1 := pow_le_one₀ hs0.le hs1
  have hsne : s ^ (4 : ℕ) ≠ 0 := ne_of_gt hs4
  have hthne : theta ≠ 0 := ne_of_gt hth
  have key : b / (s ^ (4 : ℕ) * theta) * theta = b / s ^ (4 : ℕ) := by field_simp
  rw [div_le_iff₀ hth, key, le_div_iff₀ hs4]
  have h1 : a * s ^ (4 : ℕ) ≤ a * 1 := mul_le_mul_of_nonneg_left hs4le ha
  linarith only [h1, hab]

/-- The large-waves lane's Appendix-D level, majorised. -/
private theorem laneA_bound {G Sp X Y C : ℝ} (hG : 0 ≤ G) (hSp : 0 ≤ Sp)
    (hY0 : 0 ≤ Y) (hX : X ≤ 1 + C) (hY : Y ≤ 3) (hC : 0 ≤ 1 + C) :
    G * Sp * 1 * (9 * ((1 : ℝ) / 2)⁻¹ * X * Y) ≤ 54 * (1 + C) * G * Sp := by
  have h1 : X * Y ≤ (1 + C) * 3 := mul_le_mul hX hY hY0 hC
  have hfac : (0 : ℝ) ≤ 18 * (G * Sp) := mul_nonneg (by norm_num) (mul_nonneg hG hSp)
  calc G * Sp * 1 * (9 * ((1 : ℝ) / 2)⁻¹ * X * Y)
      = 18 * (G * Sp) * (X * Y) := by
        rw [show ((1 : ℝ) / 2)⁻¹ = (2 : ℝ) by norm_num]; ring
    _ ≤ 18 * (G * Sp) * ((1 + C) * 3) := mul_le_mul_of_nonneg_left h1 hfac
    _ = 54 * (1 + C) * G * Sp := by ring

/-- The small-waves lane's Appendix-D level, majorised. -/
private theorem laneB_bound {G Sp SW X Y C s : ℝ} (hG : 0 ≤ G) (hSp : 0 ≤ Sp)
    (hSW : 0 ≤ SW) (hY0 : 0 ≤ Y) (hX : X ≤ 1 + C) (hY : Y ≤ 3) (hC : 0 ≤ 1 + C)
    (hs0 : 0 < s) :
    G * Sp * SW * (9 * (s / 8)⁻¹ * X * Y) ≤ 216 * (1 + C) * G * SW * Sp / s := by
  have h1 : X * Y ≤ (1 + C) * 3 := mul_le_mul hX hY hY0 hC
  have hfac : (0 : ℝ) ≤ 72 * (G * Sp * SW) / s :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hG hSp) hSW)) hs0.le
  calc G * Sp * SW * (9 * (s / 8)⁻¹ * X * Y)
      = 72 * (G * Sp * SW) / s * (X * Y) := by rw [inv_div]; ring
    _ ≤ 72 * (G * Sp * SW) / s * ((1 + C) * 3) := mul_le_mul_of_nonneg_left h1 hfac
    _ = 216 * (1 + C) * G * SW * Sp / s := by ring

/-! ## 3. The explicit threshold constant and majorant -/

/-- The `d`- and `r`-only prefactor of the closed `𝒢₁` threshold.  The first
summand carries the large-waves lane (`54² · 66` times the squared Appendix-D
normaliser), the second the small-waves lane (`24 · 216 · 8 · 262` times the
`Γ₁` amplitude of the two-index array). -/
def g1ThresholdConst (d : ℕ) (r : ℕ) : ℝ :=
  (192456 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ)
      + 10865664 * (1 + Cstar) * gammaMomentConst 1
          * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ))
    * ((r : ℝ) * (Real.log (6 * (r : ℝ)) + (r : ℝ)))

/-- The explicit `𝒢₁` threshold majorant: `T₀ = √(K(d,r)(1+c₁)/(s⁴θ))`. -/
def g1Majorant (d : ℕ) (r : ℕ) (s theta c1 : ℝ) : ℝ :=
  Real.sqrt (g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta))

private theorem g1ThresholdFactor_pos (d : ℕ) :
    0 < 192456 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ)
      + 10865664 * (1 + Cstar) * gammaMomentConst 1
          * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ) := by
  have hC : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hg2 : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hg1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hdlog : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hlog
  have hd : (0 : ℝ) < 1 + 2 * (d : ℝ) * Real.log 3 := by linarith only [hdlog]
  have hA : (0 : ℝ) < atomG1bScale ^ (2 : ℕ) := pow_pos atomG1bScale_pos 2
  have t1 : (0 : ℝ) < 192456 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hC 2)) (pow_pos hg2 2)
  have t2 : (0 : ℝ) < 10865664 * (1 + Cstar) * gammaMomentConst 1
      * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hC) hg1) hd) hA
  linarith only [t1, t2]

theorem g1ThresholdConst_nonneg (d r : ℕ) : 0 ≤ g1ThresholdConst d r :=
  mul_nonneg (g1ThresholdFactor_pos d).le
    (mul_nonneg (Nat.cast_nonneg r) (logSixMul_nonneg r))

theorem g1ThresholdConst_pos (d : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    0 < g1ThresholdConst d r := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hlog := Real.log_nonneg (by linarith only [hrR] : (1 : ℝ) ≤ 6 * (r : ℝ))
  exact mul_pos (g1ThresholdFactor_pos d)
    (mul_pos (by linarith only [hrR]) (by linarith only [hlog, hrR]))

theorem g1Majorant_nonneg (d r : ℕ) (s theta c1 : ℝ) :
    0 ≤ g1Majorant d r s theta c1 := Real.sqrt_nonneg _

/-! ## 4. The `𝒢₁` proportion tail at the explicit threshold -/

/-- **The `𝒢₁` proportion tail above the explicit majorant.**

Every parameter slot of `ratioTail_eventG1` is discharged here at a general
dependence range `r ≥ 1`: the moment exponents are
`p = 64 r Λ/θ + 2` and `p₂ = 256 r Λ/(sθ) + 8/s + 1` with
`Λ = log(6r) + c₁ r`, the Appendix-D normalisers are the two lanes' own
`Γ`-moment products, and both threshold conditions follow from
`T ≥ g1Majorant d r s θ c₁`. -/
theorem ratioTail_eventG1_of_majorant (M : ABKModel d) {s theta c1 T : ℝ} {r : ℕ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hr1 : 1 ≤ r) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hT : g1Majorant d r s theta c1 ≤ T) (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Support.eventG1 M k s T)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith only [hrR]
  have hthne : theta ≠ 0 := ne_of_gt htheta0
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hstpos : (0 : ℝ) < s * theta := mul_pos hs0 htheta0
  -- `θ ≤ 1/2` and the halved admissibility slot
  have hth12 : theta ≤ 1 / 2 := by
    have h2 : theta * 2 ≤ theta * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hrR]) htheta0.le
    linarith only [h2, hthetar]
  have hthetar2 : theta / 2 * ((r : ℝ) + 1) < 1 := by
    have h := mul_le_mul_of_nonneg_right
      (show theta / 2 ≤ theta by linarith only [htheta0])
      (show (0 : ℝ) ≤ (r : ℝ) + 1 by linarith only [hrR])
    linarith only [h, hthetar]
  -- the rate `Λ = log(6r) + c₁ r ≥ 1`
  set Lam : ℝ := Real.log (6 * (r : ℝ)) + c1 * (r : ℝ) with hLamdef
  have hlog6 : (1 : ℝ) < Real.log 6 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 6)]
    linarith only [Real.exp_one_lt_d9]
  have hlog6r : Real.log 6 ≤ Real.log (6 * (r : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith only [hrR])
  have hlogr : (0 : ℝ) ≤ Real.log (6 * (r : ℝ)) := by linarith only [hlog6, hlog6r]
  have hc1r : (0 : ℝ) ≤ c1 * (r : ℝ) := mul_nonneg hc1 hr0.le
  have hLam1 : (1 : ℝ) ≤ Lam := by
    rw [hLamdef]; linarith only [hlog6, hlog6r, hc1r]
  have hrLam : (1 : ℝ) ≤ (r : ℝ) * Lam := by
    have h := mul_le_mul hrR hLam1 (by norm_num) hr0.le
    linarith only [h]
  -- the two normalised exponents
  set U : ℝ := (r : ℝ) * Lam / theta with hUdef
  set V : ℝ := (r : ℝ) * Lam / (s * theta) with hVdef
  have hU1 : (1 : ℝ) ≤ U := by
    rw [hUdef, le_div_iff₀ htheta0]; linarith only [hrLam, hth12]
  have hUt : 1 / theta ≤ U := by
    rw [hUdef, le_div_iff₀ htheta0]
    have heq : 1 / theta * theta = 1 := by field_simp
    rw [heq]; exact hrLam
  have hV1 : (1 : ℝ) ≤ V := by
    rw [hVdef, le_div_iff₀ hstpos]
    have hst : s * theta ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_right hs1 htheta0.le
      linarith only [h, hth12]
    linarith only [hrLam, hst]
  have hVt : 1 / theta ≤ V := by
    rw [hVdef, le_div_iff₀ hstpos]
    have heq : 1 / theta * (s * theta) = s := by field_simp
    rw [heq]; linarith only [hrLam, hs1]
  have hVs : 2 / s ≤ V := by
    rw [hVdef, le_div_iff₀ hstpos]
    have heq : 2 / s * (s * theta) = 2 * theta := by field_simp
    rw [heq]; linarith only [hrLam, hth12]
  have hUtheta : U * theta = (r : ℝ) * Lam := by rw [hUdef]; field_simp
  have hVst : V * (s * theta) = (r : ℝ) * Lam := by rw [hVdef]; field_simp
  -- the moment exponents
  set p : ℝ := 64 * U + 2 with hpdef
  set p2 : ℝ := 256 * V + 8 / s + 1 with hp2def
  have hsinv : (1 : ℝ) ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith only [hs1]
  have h8s : (0 : ℝ) ≤ 8 / s := div_nonneg (by norm_num) hs0.le
  have hp2le : (2 : ℝ) ≤ p := by rw [hpdef]; linarith only [hU1]
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp2le]
  have hp0 : (0 : ℝ) < p := by linarith only [hp2le]
  have hsp : (1 : ℝ) ≤ 1 / 2 * p := by linarith only [hp2le]
  have hp2one : (1 : ℝ) ≤ p2 := by rw [hp2def]; linarith only [hV1, h8s]
  have hp2pos : (0 : ℝ) < p2 := by linarith only [hp2one]
  have hsp2 : (1 : ℝ) ≤ s / 8 * p2 := by
    have heq : s / 8 * p2 = 32 * (s * V) + 1 + s / 8 := by
      rw [hp2def]; field_simp; ring
    rw [heq]
    have hsV : (0 : ℝ) ≤ s * V := mul_nonneg hs0.le (by linarith only [hV1])
    linarith only [hsV, hs0]
  -- the two Appendix-D normalisers
  have hG2pos : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hG1pos : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
  set D : ℝ := gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ * 1 with hDdef
  set D2 : ℝ := gammaMomentConst 1 * p2 ^ (1 : ℝ)⁻¹ * smallWaveScale d s with hD2def
  have hDpos : (0 : ℝ) < D := by
    rw [hDdef, mul_one]; exact mul_pos hG2pos (Real.rpow_pos_of_pos hp0 _)
  have hD2pos : (0 : ℝ) < D2 := by
    rw [hD2def]
    exact mul_pos (mul_pos hG1pos (Real.rpow_pos_of_pos hp2pos _))
      (smallWaveScale_pos d hs0)
  -- the two rate conditions
  have hr16 : (0 : ℝ) < 16 * (r : ℝ) := by linarith only [hr0]
  have hratea : Lam ≤ 1 / 2 * p * (theta / 2) / (16 * (r : ℝ)) := by
    rw [le_div_iff₀ hr16]
    have hexp : 1 / 2 * p * (theta / 2) = 16 * (U * theta) + theta / 2 := by
      rw [hpdef]; ring
    rw [hexp, hUtheta]
    linarith only [htheta0]
  have hrateb : Lam ≤ s / 8 * p2 * (theta / 2) / (16 * (r : ℝ)) := by
    rw [le_div_iff₀ hr16]
    have hexp : s / 8 * p2 * (theta / 2)
        = 16 * (V * (s * theta)) + theta / 2 + s * theta / 16 := by
      rw [hp2def]; field_simp; ring
    rw [hexp, hVst]
    linarith only [htheta0, hstpos]
  -- the transcendental inputs of the two threshold conditions
  have hx0 : (0 : ℝ) < theta / 2 := by linarith only [htheta0]
  have hx1 : theta / 2 ≤ 1 := by linarith only [hth12]
  have hxinv : 1 / (theta / 2) = 2 / theta := by field_simp
  have hinvp : 1 / (theta / 2) ≤ p := by
    rw [hxinv, hpdef]
    have heq : (2 : ℝ) / theta = 2 * (1 / theta) := by ring
    linarith only [hUt, heq, hU1]
  have hinvp2 : 1 / (theta / 2) ≤ p2 := by
    rw [hxinv, hp2def]
    have heq : (2 : ℝ) / theta = 2 * (1 / theta) := by ring
    linarith only [hVt, heq, h8s, hV1]
  have hCpos1 : (0 : ℝ) < 1 + Cstar := by linarith only [Cstar_pos]
  have hCst : Cstar ^ (1 / p) ≤ 1 + Cstar := rpow_one_div_le_one_add Cstar_pos.le hp1
  have hCst2 : Cstar ^ (1 / p2) ≤ 1 + Cstar := rpow_one_div_le_one_add Cstar_pos.le hp2one
  have hthr3 : (theta / 2) ^ (-1 / p) ≤ 3 := rpow_neg_inv_le_three hx0 hx1 hinvp
  have hthr3' : (theta / 2) ^ (-1 / p2) ≤ 3 := rpow_neg_inv_le_three hx0 hx1 hinvp2
  have hthrnn : (0 : ℝ) ≤ (theta / 2) ^ (-1 / p) := Real.rpow_nonneg hx0.le _
  have hthrnn2 : (0 : ℝ) ≤ (theta / 2) ^ (-1 / p2) := Real.rpow_nonneg hx0.le _
  -- the closed-form constant, split into its two lanes
  set K1 : ℝ := 192456 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ) with hK1def
  set K2 : ℝ := 10865664 * (1 + Cstar) * gammaMomentConst 1
      * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ) with hK2def
  set Q : ℝ := (r : ℝ) * (Real.log (6 * (r : ℝ)) + (r : ℝ)) with hQdef
  have hKeq : g1ThresholdConst d r = (K1 + K2) * Q := by
    rw [hK1def, hK2def, hQdef, g1ThresholdConst]
  have hK1nn : (0 : ℝ) ≤ K1 := by
    rw [hK1def]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hCpos1.le 2))
      (pow_nonneg hG2pos.le 2)
  have hK2nn : (0 : ℝ) ≤ K2 := by
    rw [hK2def]
    have hdlog : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
        (Real.log_nonneg (by norm_num))
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpos1.le)
      hG1pos.le) (by linarith only [hdlog])) (pow_nonneg atomG1bScale_pos.le 2)
  have hc1' : (0 : ℝ) ≤ 1 + c1 := by linarith only [hc1]
  have hQ0 : (0 : ℝ) ≤ Q := by
    rw [hQdef]; exact mul_nonneg hr0.le (by linarith only [hlogr, hr0])
  have hQc : (0 : ℝ) ≤ Q * (1 + c1) := mul_nonneg hQ0 hc1'
  have hrLamQ : (r : ℝ) * Lam ≤ Q * (1 + c1) := by
    rw [hQdef, hLamdef]
    have h1 : (0 : ℝ) ≤ c1 * Real.log (6 * (r : ℝ)) := mul_nonneg hc1 hlogr
    have h2 : (0 : ℝ) ≤ (r : ℝ) * (c1 * Real.log (6 * (r : ℝ)) + (r : ℝ)) :=
      mul_nonneg hr0.le (by linarith only [h1, hr0])
    linarith only [h2]
  have hbound1 : K1 * ((r : ℝ) * Lam) ≤ (K1 + K2) * Q * (1 + c1) := by
    have s1 : K1 * ((r : ℝ) * Lam) ≤ K1 * (Q * (1 + c1)) :=
      mul_le_mul_of_nonneg_left hrLamQ hK1nn
    have s2 : (0 : ℝ) ≤ K2 * (Q * (1 + c1)) := mul_nonneg hK2nn hQc
    linarith only [s1, s2]
  have hbound2 : K2 * ((r : ℝ) * Lam) ≤ (K1 + K2) * Q * (1 + c1) := by
    have s1 : K2 * ((r : ℝ) * Lam) ≤ K2 * (Q * (1 + c1)) :=
      mul_le_mul_of_nonneg_left hrLamQ hK2nn
    have s2 : (0 : ℝ) ≤ K1 * (Q * (1 + c1)) := mul_nonneg hK1nn hQc
    linarith only [s1, s2]
  have hden : (0 : ℝ) < s ^ (4 : ℕ) * theta := mul_pos (pow_pos hs0 4) htheta0
  have harg0 : (0 : ℝ) ≤ g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta) :=
    div_nonneg (mul_nonneg (g1ThresholdConst_nonneg d r) hc1') hden.le
  have hMajsq : g1Majorant d r s theta c1 ^ (2 : ℕ)
      = g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta) := Real.sq_sqrt harg0
  -- lane: the large-waves threshold
  set A : ℝ := 54 * (1 + Cstar) * gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ with hAdef
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hAdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpos1.le) hG2pos.le)
      (Real.rpow_nonneg hp0.le _)
  have hlanea : D * (9 * ((1 : ℝ) / 2)⁻¹ * Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p))
      ≤ A := by
    rw [hDdef, hAdef]
    exact laneA_bound hG2pos.le (Real.rpow_nonneg hp0.le _) hthrnn hCst hthr3 hCpos1.le
  have hsq : (p ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) = p := by
    have hsqrtp : p ^ (2 : ℝ)⁻¹ = Real.sqrt p := by rw [Real.sqrt_eq_rpow]; norm_num
    rw [hsqrtp]; exact Real.sq_sqrt hp0.le
  have hAsq : A ^ (2 : ℕ)
      = 2916 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ) * p :=
    calc A ^ (2 : ℕ)
        = (54 * (1 + Cstar) * gammaMomentConst 2) ^ (2 : ℕ) * (p ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) := by
          rw [hAdef, ← mul_pow]
      _ = (54 * (1 + Cstar) * gammaMomentConst 2) ^ (2 : ℕ) * p := by rw [hsq]
      _ = 2916 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ) * p := by ring
  have hple : p ≤ 66 * U := by rw [hpdef]; linarith only [hU1]
  have hAsqle : A ^ (2 : ℕ) ≤ K1 * U := by
    rw [hAsq, hK1def]
    have hfac : (0 : ℝ) ≤ 2916 * (1 + Cstar) ^ (2 : ℕ) * gammaMomentConst 2 ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hCpos1.le 2))
        (pow_nonneg hG2pos.le 2)
    have h := mul_le_mul_of_nonneg_left hple hfac
    linarith only [h]
  have hAle : A ≤ g1Majorant d r s theta c1 := by
    rw [g1Majorant]
    refine le_sqrt_of_sq_le hA0 ?_
    rw [hKeq]
    have hUeq : K1 * U = K1 * ((r : ℝ) * Lam) / theta := by rw [hUdef]; ring
    have hstep : K1 * ((r : ℝ) * Lam) / theta
        ≤ (K1 + K2) * Q * (1 + c1) / (s ^ (4 : ℕ) * theta) :=
      div_le_div_pow_four (mul_nonneg hK1nn (by linarith only [hrLam])) hbound1 hs0 hs1
        htheta0
    rw [hUeq] at hAsqle
    exact le_trans hAsqle hstep
  have hthra : D * (9 * ((1 : ℝ) / 2)⁻¹ * Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p))
      ≤ T := le_trans hlanea (le_trans hAle hT)
  -- lane (b): the small-waves threshold
  set Pc : ℝ := (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ) with hPcdef
  set B : ℝ := 216 * (1 + Cstar) * gammaMomentConst 1 * smallWaveScale d s * p2 / s
    with hBdef
  have hSWpos : (0 : ℝ) < smallWaveScale d s := smallWaveScale_pos d hs0
  have hlaneb : D2 * (9 * (s / 8)⁻¹ * Cstar ^ (1 / p2) * (theta / 2) ^ (-1 / p2))
      ≤ B := by
    have hp2rpow : p2 ^ (1 : ℝ)⁻¹ = p2 := by rw [inv_one, Real.rpow_one]
    calc D2 * (9 * (s / 8)⁻¹ * Cstar ^ (1 / p2) * (theta / 2) ^ (-1 / p2))
        ≤ 216 * (1 + Cstar) * gammaMomentConst 1 * smallWaveScale d s
            * p2 ^ (1 : ℝ)⁻¹ / s := by
          rw [hD2def]
          exact laneB_bound hG1pos.le (Real.rpow_nonneg hp2pos.le _) hSWpos.le hthrnn2
            hCst2 hthr3' hCpos1.le hs0
      _ = B := by rw [hBdef, hp2rpow]
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      hCpos1.le) hG1pos.le) hSWpos.le) hp2pos.le) hs0.le
  have hSWeq : smallWaveScale d s = 8 * Pc / s := by
    have h : smallWaveScale d s
        = 8 / s * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ (2 : ℕ) := rfl
    rw [h, hPcdef]; ring
  have hp2V : p2 ≤ 262 * V := by
    have h12 : 12 / s ≤ 6 * V := by
      have h := mul_le_mul_of_nonneg_left hVs (by norm_num : (0 : ℝ) ≤ 6)
      have heq : (6 : ℝ) * (2 / s) = 12 / s := by ring
      linarith only [h, heq]
    have h4 : (1 : ℝ) ≤ 4 / s := by rw [le_div_iff₀ hs0]; linarith only [hs1]
    have heq2 : (8 : ℝ) / s + 4 / s = 12 / s := by ring
    rw [hp2def]
    linarith only [h12, h4, heq2]
  have hFac0 : (0 : ℝ) ≤ 41472 * (1 + Cstar) * gammaMomentConst 1 * Pc / s ^ (3 : ℕ) := by
    have hPc0 : (0 : ℝ) ≤ Pc := by
      rw [hPcdef]
      have hdlog : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
          (Real.log_nonneg (by norm_num))
      exact mul_nonneg (by linarith only [hdlog]) (pow_nonneg atomG1bScale_pos.le 2)
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpos1.le)
      hG1pos.le) hPc0) (pow_nonneg hs0.le 3)
  have hstep2 : 24 / s * B ≤ K2 * ((r : ℝ) * Lam) / (s ^ (4 : ℕ) * theta) := by
    calc 24 / s * B
        = 41472 * (1 + Cstar) * gammaMomentConst 1 * Pc / s ^ (3 : ℕ) * p2 := by
          rw [hBdef, hSWeq]; field_simp; ring
      _ ≤ 41472 * (1 + Cstar) * gammaMomentConst 1 * Pc / s ^ (3 : ℕ) * (262 * V) :=
          mul_le_mul_of_nonneg_left hp2V hFac0
      _ = K2 * ((r : ℝ) * Lam) / (s ^ (4 : ℕ) * theta) := by
          rw [hK2def, hPcdef, ← hVst]; field_simp; ring
  have hlaneb2 : g1bConst s * B ≤ g1Majorant d r s theta c1 ^ (2 : ℕ) := by
    refine le_trans (le_trans (mul_le_mul_of_nonneg_right
      (g1bConst_le_of_le_one hs0 hs1) hB0) hstep2) ?_
    rw [hMajsq, hKeq]
    exact div_le_div_right_of_le hbound2 hden
  have hMajT2 : g1Majorant d r s theta c1 ^ (2 : ℕ) ≤ T ^ 2 :=
    pow_le_pow_left₀ (g1Majorant_nonneg d r s theta c1) hT 2
  have hthrb : D2 * (9 * (s / 8)⁻¹ * Cstar ^ (1 / p2) * (theta / 2) ^ (-1 / p2))
      ≤ T ^ 2 / g1bConst s := by
    rw [le_div_iff₀ (g1bConst_pos hs0)]
    have h1 := mul_le_mul_of_nonneg_right hlaneb (g1bConst_pos hs0).le
    linarith only [h1, hlaneb2, hMajT2]
  exact ratioTail_eventG1 M hs0 hs1 hDpos hD2pos hp1 hp2one hsp hsp2 hr1 htheta0
    hthetar2 hc1 hratea hrateb hDdef.ge hD2def.ge hthra hthrb n

/-! ## 5. The certificate against the Section 4 support threshold -/

/-- **The majorant sits below the frozen `𝒢₁` threshold.**

The right-hand side `s ε √(c⋆) (√γ)⁻¹` is exactly the threshold at which
`Support.goodEventBase` instantiates `𝒢₁`. -/
theorem g1Majorant_le_shellThreshold (M : ABKModel d) {s ep theta c1 : ℝ} {r : ℕ}
    (hs0 : 0 < s) (hep0 : 0 < ep) (htheta0 : 0 < theta) (hc1 : 0 ≤ c1)
    (hcond : g1ThresholdConst d r * (1 + c1) * M.gamma
        ≤ theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) :
    g1Majorant d r s theta c1
      ≤ s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hden : (0 : ℝ) < s ^ (4 : ℕ) * theta := mul_pos (pow_pos hs0 4) htheta0
  have hc1' : (0 : ℝ) ≤ 1 + c1 := by linarith only [hc1]
  have harg0 : (0 : ℝ) ≤ g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta) :=
    div_nonneg (mul_nonneg (g1ThresholdConst_nonneg d r) hc1') hden.le
  have hRHS0 : (0 : ℝ) ≤ s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hs0.le hep0.le) (Real.sqrt_nonneg _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hMajsq : g1Majorant d r s theta c1 ^ (2 : ℕ)
      = g1ThresholdConst d r * (1 + c1) / (s ^ (4 : ℕ) * theta) := Real.sq_sqrt harg0
  have hRsq : (s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ (2 : ℕ)
      = s ^ (2 : ℕ) * ep ^ (2 : ℕ) * Disorder.cstar M / M.gamma := by
    rw [mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hcs0.le, Real.sq_sqrt hgam0.le]
    ring
  refine le_of_sq_le_sq (g1Majorant_nonneg d r s theta c1) hRHS0 ?_
  rw [hMajsq, hRsq, div_le_iff₀ hden]
  have hrw : s ^ (2 : ℕ) * ep ^ (2 : ℕ) * Disorder.cstar M / M.gamma * (s ^ (4 : ℕ) * theta)
      = theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / M.gamma := by
    field_simp
  rw [hrw, le_div_iff₀ hgam0]
  exact hcond

/-- **The `𝒢₁` proportion tail at the frozen support threshold.**  Targets 2 and
3 combined: under the explicit parameter condition `hcond`, the `𝒢₁` bad-scale
density at the threshold `s ε √(c⋆) (√γ)⁻¹` obeys the `exp(-c₁n)/3` tail. -/
theorem ratioTail_eventG1_shellThreshold (M : ABKModel d) {s ep theta c1 : ℝ} {r : ℕ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hep0 : 0 < ep) (hr1 : 1 ≤ r) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hcond : g1ThresholdConst d r * (1 + c1) * M.gamma
        ≤ theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k =>
          (Support.eventG1 M k s
            (s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))ᶜ)
            n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) :=
  ratioTail_eventG1_of_majorant M hs0 hs1 hr1 htheta0 hthetar hc1
    (g1Majorant_le_shellThreshold M hs0 hep0 htheta0 hc1 hcond) n

end

end Algsuperdiff.Section4.Provider.Proportion
