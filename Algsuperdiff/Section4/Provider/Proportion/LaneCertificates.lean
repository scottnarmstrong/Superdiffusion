/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.RatioTailUniform
import Algsuperdiff.Section4.Provider.Proportion.G1ThresholdArith
import Algsuperdiff.Section4.Provider.Proportion.LaneInterface

/-!
# The two proved lane certificates, at one common dependence range

ABK26, §4.1.  `RatioTailUniform.exists_ratioTail_eventG0_uniform` and
`G1ThresholdArith.ratioTail_eventG1_shellThreshold` are the two proved
per-event ratio-tail endpoints.  This module puts them in the single `LaneTail`
shape that the three-fold union bound of `p.independence.between.scales`
consumes, at **one** dependence range `r = r(d)` and **one** constant `C(d)`
chosen before every parameter, and composes them with the `𝒢₂` lane's
`LaneTail` slot.

## The two couplings

Both lanes are unconditional in everything probabilistic; what each still needs
is one explicit inequality tying the model to the level `θ` and the rate `c₁`:

* `𝒢₀`: `C⁹γ² ≤ θ c⋆⁸` — the level-vs-regime coupling that replaces the proved
  `RatioTailClosed` packaging of `θ` *inside* the constant.  It is derivable
  from the frozen proportion anchor's own clauses (`couplingG0_of_anchor`
  below).
* `𝒢₁`: `K(d,r)(1+c₁)γ ≤ θ c⋆ s⁶ ε²` — the closed form of `T₀ ≤ s ε √c⋆
  γ^{-1/2}` at the substituted threshold of `e.lambda.good.events`.

## References

* ABK26, `p.independence.between.scales`; `l.good.scales.ratio.lambda`;
  `l.ratio.of.good.scales.for.k`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open Homogenization Homogenization.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The `𝒢₀` lane certificate -/

/-- **The `𝒢₀` lane in `LaneTail` shape**, with one dependence range `r(d)` and
one constant `C(d)` chosen before the level, the rate and the model.  This is
`RatioTailUniform.exists_ratioTail_eventG0_uniform` read through `LaneTail`. -/
theorem exists_laneTail_eventG0 (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 6 ≤ C ∧
      ∀ (M : ABKModel d) (theta c1 : ℝ),
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        0 < theta → theta * ((r : ℝ) + 1) < 1 →
        C ^ (9 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) →
        0 ≤ c1 → c1 * M.gamma ≤ 1 →
        LaneTail M (fun k => Support.eventG0 M (Support.cgEllipLowerConstant d) k)
          theta c1 := by
  obtain ⟨r, hr1, C, hC6, hall⟩ := exists_ratioTail_eventG0_uniform d
  exact ⟨r, hr1, C, hC6, fun M theta c1 hreg htheta0 hthetar hcouple hc10 hc1g =>
    hall M hreg theta htheta0 hthetar hcouple c1 hc10 hc1g⟩

/-! ## 2. The frozen-anchor bridge arithmetic

Two abstract-real implications recording what the frozen proportion anchor's own
parameter clauses give.  The anchor quantifies one constant `C_a` before
`(M, s, ε, θ)` and carries the regime `γ ≤ C_a^{-1}c⋆^{10}` together with the
level clause `C_a c⋆^{-2}s^{-4}ε^{-2}γ ≤ θ`. -/

/-- So one `C(d)` before the parameters costs nothing on this lane. -/
theorem couplingG0_of_anchor {C Ca cs s ep theta gamma : ℝ}
    (hC : 6 ≤ C) (hcs0 : 0 < cs) (hcs32 : cs ≤ 3 / 2)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2)
    (hg0 : 0 < gamma) (hCa : C ^ (5 : ℕ) ≤ Ca)
    (hreg : gamma ≤ Ca⁻¹ * cs ^ (10 : ℕ))
    (hthetacond : Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (4 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma ≤ theta) :
    C ^ (10 : ℕ) * gamma ^ (2 : ℕ) ≤ theta * cs ^ (8 : ℕ) := by
  have hC0 : (0 : ℝ) < C := by linarith only [hC]
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le (by positivity) hCa
  have hcs8 : (0 : ℝ) ≤ cs ^ (8 : ℕ) := by positivity
  have hA : (4 / 9 : ℝ) ≤ (cs⁻¹) ^ (2 : ℕ) := by
    have h : (2 / 3 : ℝ) ≤ cs⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hcs0]
      calc cs ≤ 3 / 2 := hcs32
        _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
    calc (4 / 9 : ℝ) = (2 / 3 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (cs⁻¹) ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) h 2
  have hB : (16 : ℝ) ≤ (s⁻¹) ^ (4 : ℕ) := by
    have h : (2 : ℝ) ≤ s⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hs0]
      calc s ≤ 1 / 2 := hs12
        _ = (2 : ℝ)⁻¹ := by norm_num
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (s⁻¹) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) h 4
  have hE : (4 : ℝ) ≤ (ep⁻¹) ^ (2 : ℕ) := by
    have h : (2 : ℝ) ≤ ep⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hep0]
      calc ep ≤ 1 / 2 := hep12
        _ = (2 : ℝ)⁻¹ := by norm_num
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (ep⁻¹) ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) h 2
  have hCg : (0 : ℝ) ≤ Ca * gamma := by positivity
  have hlow : 28 * Ca * gamma ≤ theta := by
    refine le_trans ?_ hthetacond
    calc 28 * Ca * gamma = 28 * (Ca * gamma) := by ring
      _ ≤ 256 / 9 * (Ca * gamma) := mul_le_mul_of_nonneg_right (by norm_num) hCg
      _ = Ca * (4 / 9) * 16 * 4 * gamma := by ring
      _ ≤ Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (4 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma := by gcongr
  have hCasq : C ^ (10 : ℕ) ≤ Ca ^ (2 : ℕ) := by
    calc C ^ (10 : ℕ) = (C ^ (5 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ Ca ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hCa 2
  have hkey : Ca * gamma ≤ cs ^ (10 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hreg hCa0.le
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hCa0), one_mul] at h
  have hstep : Ca * (C ^ (10 : ℕ) * gamma ^ (2 : ℕ))
      ≤ Ca * (28 * Ca * gamma * cs ^ (8 : ℕ)) := by
    have h2 : C ^ (10 : ℕ) * gamma * (Ca * gamma) ≤ C ^ (10 : ℕ) * gamma * cs ^ (10 : ℕ) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have hcssq : cs ^ (10 : ℕ) ≤ 9 / 4 * cs ^ (8 : ℕ) := by
      have h : cs ^ (2 : ℕ) ≤ 9 / 4 := by
        calc cs ^ (2 : ℕ) ≤ (3 / 2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hcs0.le hcs32 2
          _ = 9 / 4 := by norm_num
      calc cs ^ (10 : ℕ) = cs ^ (8 : ℕ) * cs ^ (2 : ℕ) := by ring
        _ ≤ cs ^ (8 : ℕ) * (9 / 4) := mul_le_mul_of_nonneg_left h hcs8
        _ = 9 / 4 * cs ^ (8 : ℕ) := by ring
    have h3 : C ^ (10 : ℕ) * gamma * cs ^ (10 : ℕ)
        ≤ C ^ (10 : ℕ) * gamma * (9 / 4 * cs ^ (8 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcssq (by positivity)
    have h4 : 9 / 4 * (C ^ (10 : ℕ) * gamma * cs ^ (8 : ℕ))
        ≤ 28 * (Ca ^ (2 : ℕ) * gamma * cs ^ (8 : ℕ)) := by
      have hmono : C ^ (10 : ℕ) * gamma * cs ^ (8 : ℕ)
          ≤ Ca ^ (2 : ℕ) * gamma * cs ^ (8 : ℕ) := by gcongr
      linarith only [hmono,
        mul_nonneg (mul_nonneg (pow_nonneg hCa0.le 2) hg0.le) hcs8]
    calc Ca * (C ^ (10 : ℕ) * gamma ^ (2 : ℕ)) = C ^ (10 : ℕ) * gamma * (Ca * gamma) := by ring
      _ ≤ C ^ (10 : ℕ) * gamma * cs ^ (10 : ℕ) := h2
      _ ≤ C ^ (10 : ℕ) * gamma * (9 / 4 * cs ^ (8 : ℕ)) := h3
      _ = 9 / 4 * (C ^ (10 : ℕ) * gamma * cs ^ (8 : ℕ)) := by ring
      _ ≤ 28 * (Ca ^ (2 : ℕ) * gamma * cs ^ (8 : ℕ)) := h4
      _ = Ca * (28 * Ca * gamma * cs ^ (8 : ℕ)) := by ring
  calc C ^ (10 : ℕ) * gamma ^ (2 : ℕ) ≤ 28 * Ca * gamma * cs ^ (8 : ℕ) :=
        le_of_mul_le_mul_left hstep hCa0
    _ ≤ theta * cs ^ (8 : ℕ) := mul_le_mul_of_nonneg_right hlow hcs8

/-- The two hypotheses are **not** the printed ones: the manuscript's
`e.theta.cond.two` and the frozen theorem's clauses carry `s^{-4}` and `s⁵`.
Nothing downstream consumes the printed condition. -/
theorem couplingG1_of_anchor {K Ca cs s ep theta gamma c1 : ℝ}
    (hK0 : 0 < K) (hcs0 : 0 < cs) (hcs32 : cs ≤ 3 / 2)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep)
    (hg0 : 0 < gamma) (hCa : 3 * K ≤ Ca)
    (hthetacond : Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (6 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma ≤ theta)
    (hrate : Ca * (c1 * gamma) ≤ cs ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta) :
    K * (1 + c1) * gamma ≤ theta * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by
  have hK : (0 : ℝ) < 3 * K := by linarith only [hK0]
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le hK hCa
  have hQ0 : (0 : ℝ) < cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by positivity
  have h1 : Ca * gamma * cs⁻¹ ≤ theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by
    have hmul := mul_le_mul_of_nonneg_right hthetacond hQ0.le
    calc Ca * gamma * cs⁻¹
        = Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (6 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma *
            (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by
          field_simp
      _ ≤ theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := hmul
  have hcsinv : (2 : ℝ) / 3 ≤ cs⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcs0]
    calc cs ≤ 3 / 2 := hcs32
      _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
  have h2 : 2 * K * gamma ≤ Ca * gamma * cs⁻¹ := by
    have hstep : Ca * gamma * (2 / 3) ≤ Ca * gamma * cs⁻¹ :=
      mul_le_mul_of_nonneg_left hcsinv (by positivity)
    have hstep2 : 2 * K * gamma ≤ Ca * gamma * (2 / 3) := by
      have h : 3 * K * gamma ≤ Ca * gamma := mul_le_mul_of_nonneg_right hCa hg0.le
      linarith only [h]
    linarith only [hstep, hstep2]
  have h3 : 2 * (K * (c1 * gamma)) ≤ theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by
    have hcss : 2 * K * (cs * s) ≤ Ca := by
      have hprod : cs * s ≤ 3 / 4 := by
        have h := mul_le_mul hcs32 hs12 hs0.le (by norm_num : (0 : ℝ) ≤ 3 / 2)
        calc cs * s ≤ 3 / 2 * (1 / 2) := h
          _ = 3 / 4 := by norm_num
      have hK2 : 2 * K * (cs * s) ≤ 2 * K * (3 / 4) :=
        mul_le_mul_of_nonneg_left hprod (by linarith only [hK0])
      linarith only [hK2, hCa, hK0]
    have hmul : 2 * K * (Ca * (c1 * gamma))
        ≤ 2 * K * (cs ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta) :=
      mul_le_mul_of_nonneg_left hrate (by linarith only [hK0])
    have hcancel : Ca * (2 * (K * (c1 * gamma)))
        ≤ Ca * (theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ))) := by
      calc Ca * (2 * (K * (c1 * gamma))) = 2 * K * (Ca * (c1 * gamma)) := by ring
        _ ≤ 2 * K * (cs ^ (2 : ℕ) * s ^ (7 : ℕ) * ep ^ (2 : ℕ) * theta) := hmul
        _ = (2 * K * (cs * s)) * (theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ))) := by ring
        _ ≤ Ca * (theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ))) := by
            refine mul_le_mul_of_nonneg_right hcss ?_
            exact le_trans (by positivity : (0 : ℝ) ≤ 2 * K * gamma) (le_trans h2 h1)
    exact le_of_mul_le_mul_left hcancel hCa0
  have hassoc : theta * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)
      = theta * (cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) := by ring
  have hsum : K * (1 + c1) * gamma = K * gamma + K * (c1 * gamma) := by ring
  rw [hsum, hassoc]
  linarith only [h1, h2, h3]

/-- **The printed regime is absorbable.**  The anchor's regime
`γ ≤ C_a^{-1}c⋆^{10}` at any `C_a ≥ C^{10}` gives the `𝒢₀` lane's printed regime
`γ ≤ (C^{-1})^{10}c⋆^{10}`. -/
theorem regime_of_anchor {C Ca cs gamma : ℝ} (hC0 : 0 < C)
    (hCa : C ^ (10 : ℕ) ≤ Ca) (hreg : gamma ≤ Ca⁻¹ * cs ^ (10 : ℕ)) :
    gamma ≤ (C⁻¹) ^ (10 : ℕ) * cs ^ (10 : ℕ) := by
  refine le_trans hreg (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hCa

/-! ## 3. The `𝒢₁` lane certificate at the common range -/

/-- **The `𝒢₁` lane in `LaneTail` shape**, at the substituted threshold
`s ε √c⋆ (√γ)⁻¹` of `e.lambda.good.events` and at any dependence range `r ≥ 1`
(so in particular at the `𝒢₀` lane's `r(d)`).  This is
`G1ThresholdArith.ratioTail_eventG1_shellThreshold` read through `LaneTail`. -/
theorem laneTail_eventG1_shellThreshold (M : ABKModel d) {s ep theta c1 : ℝ} {r : ℕ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hep0 : 0 < ep) (hr1 : 1 ≤ r) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hcond : g1ThresholdConst d r * (1 + c1) * M.gamma
        ≤ theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) :
    LaneTail M
      (fun k => Support.eventG1 M k s
        (s * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)) theta c1 :=
  fun n => ratioTail_eventG1_shellThreshold M hs0 hs1 hep0 hr1 htheta0 hthetar hc1 hcond n

/-! ## 4. The three-lane endpoint, with the `𝒢₂` slot -/

/-- **The `§4.1` proportion premise from two proved lanes and one named slot.**

One dependence range `r(d)` and one constant `C(d)`, both fixed before every
parameter.  Both output forms are delivered: the bad-density form the union
bound produces, and the good-proportion form `avsum 𝟙{𝒢} ≤ 1 − θ` in which the
printed display is stated.

Every window `n` is covered, including the short windows `n < r`.  The rate
`c₁` is the caller's, up to the `𝒢₀` lane's ceiling `c₁γ ≤ 1` (: the rate is
delivered, not read off the printed per-lane displays). -/
theorem exists_ratioTail_goodEventBase (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, 6 ≤ C ∧
      ∀ (M : ABKModel d) (s : {s : ℝ // 0 < s}) (ep theta c1 : ℝ),
        (s : ℝ) ≤ 1 → 0 < ep → 0 < theta → theta * ((r : ℝ) + 1) < 1 →
        0 ≤ c1 → c1 * M.gamma ≤ 1 →
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        C ^ (10 : ℕ) * M.gamma ^ (2 : ℕ) ≤ theta * (Disorder.cstar M) ^ (8 : ℕ) →
        C * (1 + c1) * M.gamma
            ≤ theta * Disorder.cstar M * (s : ℝ) ^ (6 : ℕ) * ep ^ (2 : ℕ) →
        LaneTail M (fun k => Support.eventG2 M k s ep) (theta / 4) c1 →
        (∀ n : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure
                {omega | theta < scaleProp
                  (fun k =>
                    (Support.goodEventBase M (Support.cgEllipLowerConstant d) k s ep)ᶜ)
                  n omega}
              ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)))) ∧
          ∀ n : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure
                {omega | scaleProp
                  (fun k => Support.goodEventBase M (Support.cgEllipLowerConstant d) k s ep)
                  n omega ≤ 1 - theta}
              ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
  obtain ⟨r, hr1, C0, hC06, hG0⟩ := exists_laneTail_eventG0 d
  refine ⟨r, hr1, max C0 (max 6 (4 * g1ThresholdConst d r)), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  intro M s ep theta c1 hs1 hep0 htheta0 hthetar hc10 hc1g hreg hcoup hcond hG2
  have hC0le : C0 ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) := le_max_left _ _
  have hC6 : (6 : ℝ) ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hg1le : 4 * g1ThresholdConst d r ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0pos : (0 : ℝ) < C0 := by linarith only [hC06]
  have hCpos : (0 : ℝ) < max C0 (max 6 (4 * g1ThresholdConst d r)) := by linarith only [hC6]
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hth4 : (0 : ℝ) < theta / 4 := by linarith only [htheta0]
  have hthetar4 : theta / 4 * ((r : ℝ) + 1) < 1 := by
    have hrw : theta / 4 * ((r : ℝ) + 1) = theta * ((r : ℝ) + 1) / 4 := by ring
    rw [hrw]
    linarith only [hthetar]
  -- the `𝒢₀` lane at level `θ/4`
  have hlane0 : LaneTail M
      (fun k => Support.eventG0 M (Support.cgEllipLowerConstant d) k) (theta / 4) c1 := by
    refine hG0 M (theta / 4) c1 ?_ hth4 hthetar4 ?_ hc10 hc1g
    · refine le_trans hreg (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hC0pos hC0le) 10
    · have h9 : C0 ^ (9 : ℕ) ≤ (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (9 : ℕ) :=
        pow_le_pow_left₀ hC0pos.le hC0le 9
      have h10 : 4 * C0 ^ (9 : ℕ)
          ≤ (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (10 : ℕ) := by
        calc 4 * C0 ^ (9 : ℕ)
            ≤ 4 * (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (9 : ℕ) := by
              linarith only [h9]
          _ ≤ max C0 (max 6 (4 * g1ThresholdConst d r)) *
                (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (9 : ℕ) :=
              mul_le_mul_of_nonneg_right (by linarith only [hC6]) (pow_nonneg hCpos.le 9)
          _ = (max C0 (max 6 (4 * g1ThresholdConst d r))) ^ (10 : ℕ) := by ring
      have hstep := mul_le_mul_of_nonneg_right h10 (pow_nonneg hg0.le 2)
      linarith only [hstep, hcoup]
  -- the `𝒢₁` lane at level `θ/4`
  have hlane1 : LaneTail M
      (fun k => Support.eventG1 M k (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (theta / 4) c1 := by
    refine laneTail_eventG1_shellThreshold M s.2 hs1 hep0 hr1 hth4 hthetar4 hc10 ?_
    have hprod : (0 : ℝ) ≤ (1 + c1) * M.gamma := by positivity
    have h4 := mul_le_mul_of_nonneg_right hg1le hprod
    linarith only [h4, hcond]
  refine ⟨fun n => ?_, fun n => ?_⟩
  · exact measure_scaleProp_compl_goodEventBase_le M (Support.cgEllipLowerConstant d) s ep
      theta c1 (hlane0.mono_level (by linarith only [htheta0]))
      (hlane1.mono_level (by linarith only [htheta0]))
      (hG2.mono_level (by linarith only [htheta0])) n
  · exact measure_scaleProp_goodEventBase_le M (Support.cgEllipLowerConstant d) s ep
      theta c1 htheta0 hlane0 hlane1 hG2 n

end

end Algsuperdiff.Section4.Provider.Proportion
