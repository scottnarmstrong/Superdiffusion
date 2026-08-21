/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Proportion.SmallWaves

/-!
# Step 3 of `l.ratio.of.good.scales.for.k`: the `½θ` split and the `𝒢₁` tail

This module performs that recombination.  The frozen `𝒢₁(m; s, T)` *is* the
intersection `eventG1a ∩ eventG1b` (by `rfl`), and the proved
`setOf_scaleProp_inter_subset` turns a `θ`-density of `𝒢₁`-bad scales into a
`θ/2`-density for one of the two lanes.  Running each lane at prefactor `6`
recombines into the consumer's `exp(-c₁n)/3`, the same endpoint shape the `𝒢₀`
lane delivers in `RatioTailClosed.exists_ratioTail_eventG0`.

## What is closed here, and what is not

`ratioTail_eventG1` is unconditional in everything probabilistic: both lanes'
atom tails come from the Section 3 surface, both independence hypotheses from
(J1) at any `r ≥ 1`, and both rows are a.s. finite.  What it still carries are
the two lanes' **parameter conditions** — the Appendix-D normalizers `D`, `D₂`,
the moment exponents `p`, `p₂`, the rate conditions, and the two threshold
conditions relating `T` to the level `θ`.

## References

* ABK26, `l.ratio.of.good.scales.for.k`, Step 3.
* ABK26, `d.good.event.for.lambda`.
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

/-! ## 1. Sign facts for the Appendix-D threshold -/

/-- The standing assumption `γ ≤ 1/4` of `ShellLawPrefix` makes the large-waves
Appendix-D weight rate `s' = 1/2` admissible: `1/2 ≤ 1 - γ`. -/
theorem half_le_one_sub_gamma (M : ABKModel d) : (1 : ℝ) / 2 ≤ 1 - M.gamma := by
  have h := M.shellPrefix.gamma_le_quarter
  linarith only [h]


/-- The Appendix-D threshold level is nonnegative — the `hlam` slot of both
lanes' reductions. -/
theorem appendixD_level_nonneg {sprime p theta : ℝ} (hs : 0 < sprime)
    (htheta : 0 < theta) :
    0 ≤ 9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) := by
  have h1 : (0 : ℝ) ≤ 9 * sprime⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ Cstar ^ (1 / p) := Real.rpow_nonneg Cstar_pos.le _
  have h3 : (0 : ℝ) ≤ theta ^ (-1 / p) := Real.rpow_nonneg htheta.le _
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-! ## 2. The `½θ` split -/

/-- **The `½θ` recombination of the two `𝒢₁` lanes.**  This is the Lean form of
the manuscript's own bookkeeping: Steps 1 and 2 each bound a bad-density at level
`> ½θ`, and Step 3 combines them.  Run at prefactor `6` per lane, the two halves
recombine into the consumer's `exp(-c₁n)/3`. -/
theorem ratioTail_eventG1_of_lanes (M : ABKModel d) {s T theta c1 : ℝ} (n : ℕ)
    (ha : (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta / 2 < scaleProp (fun k => (eventG1a M k T)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 6))
    (hb : (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta / 2 < scaleProp (fun k => (eventG1b M k s T)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 6)) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Support.eventG1 M k s T)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  have hsplit : {omega : Cutoff.CutoffSample d |
      theta < scaleProp (fun k => (Support.eventG1 M k s T)ᶜ) n omega} ⊆
      {omega | theta / 2 < scaleProp (fun k => (eventG1a M k T)ᶜ) n omega} ∪
        {omega | theta / 2 < scaleProp (fun k => (eventG1b M k s T)ᶜ) n omega} := by
    have hEv : ∀ k : ℤ,
        Support.eventG1 M k s T = eventG1a M k T ∩ eventG1b M k s T :=
      fun k => eventG1_eq_inter M k s T
    simp only [hEv]
    exact setOf_scaleProp_inter_subset (fun k => eventG1a M k T)
      (fun k => eventG1b M k s T) n (le_of_eq (by ring))
  refine le_trans (measure_mono hsplit) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add ha hb) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith only [Real.exp_nonneg (-c1 * (n : ℝ))]

/-! ## 3. The composed `𝒢₁` proportion tail -/

/-- **The `𝒢₁` proportion tail** (`l.ratio.of.good.scales.for.k`), assembled from
the two lanes at level `θ/2` and prefactor `6`.

Everything probabilistic is discharged: the two atom families' `Γ` tails from
the Section 3 surface, the columns' independence from (J1) at the caller's `r ≥
1` (no separation geometry, no dimension restriction), the a.s. finiteness of
both Appendix-D rows, and the short-window extension.  What the caller supplies
is the parameter package: the two moment exponents `p`, `p₂`, the two Appendix-D
normalizers `D`, `D₂`, the two rate conditions and the two threshold conditions
relating `T` to `θ`. -/
theorem ratioTail_eventG1 (M : ABKModel d)
    {s T D D2 p p2 theta c1 : ℝ} {r : ℕ}
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hD : 0 < D) (hD2 : 0 < D2) (hp : 1 ≤ p) (hp2 : 1 ≤ p2)
    (hsp : 1 ≤ (1 : ℝ) / 2 * p) (hsp2 : 1 ≤ s / 8 * p2)
    (hr1 : 1 ≤ r) (htheta0 : 0 < theta)
    (hthetar : theta / 2 * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hratea : Real.log (6 * (r : ℝ)) + c1 * (r : ℝ) ≤
      (1 : ℝ) / 2 * p * (theta / 2) / (16 * (r : ℝ)))
    (hrateb : Real.log (6 * (r : ℝ)) + c1 * (r : ℝ) ≤
      s / 8 * p2 * (theta / 2) / (16 * (r : ℝ)))
    (hnorma : gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ * 1 ≤ D)
    (hnormb : gammaMomentConst 1 * p2 ^ (1 : ℝ)⁻¹ * smallWaveScale d s ≤ D2)
    (hthra : D * (9 * ((1 : ℝ) / 2)⁻¹ * Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p)) ≤ T)
    (hthrb : D2 * (9 * (s / 8)⁻¹ * Cstar ^ (1 / p2) * (theta / 2) ^ (-1 / p2)) ≤
      T ^ 2 / g1bConst s)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Support.eventG1 M k s T)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  have htheta2 : 0 < theta / 2 := by linarith only [htheta0]
  have ha := ratioTail_eventG1a M (sprime := (1 : ℝ) / 2) (T := T) (D := D) (p := p)
    (theta := theta / 2) (c1 := c1) (Q := 6) (r := r)
    (by norm_num) (by norm_num) (half_le_one_sub_gamma M) hD hp hsp hr1 (by norm_num) htheta2 hthetar hc1
    hratea hnorma
    (appendixD_level_nonneg (by norm_num) htheta2) hthra n
  have hb := ratioTail_eventG1b M (s := s) (T := T) (D := D2) (p := p2)
    (theta := theta / 2) (c1 := c1) (Q := 6) (r := r)
    hs0 hs1 hD2 hp2 hsp2 hr1 (by norm_num) htheta2 hthetar hc1 hrateb hnormb
    (appendixD_level_nonneg (by linarith only [hs0]) htheta2) hthrb n
  exact ratioTail_eventG1_of_lanes M n ha hb

/-! ## 4. Monotonicity in the threshold -/

/-- The bad-scale density is monotone in the event family. -/
theorem scaleProp_mono {Omega : Type*} {A B : ℤ → Set Omega}
    (h : ∀ m, A m ⊆ B m) (n : ℕ) (omega : Omega) :
    scaleProp A n omega ≤ scaleProp B n omega := by
  classical
  simp only [scaleProp]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
  by_cases hm : omega ∈ A m
  · rw [if_pos hm, if_pos (h m hm)]
  · rw [if_neg hm]
    split_ifs <;> norm_num

/-- **The `𝒢₁` tail is monotone in the threshold.**  `𝒢₁(m; s, T)` grows with
`T`, so its bad-scale density shrinks; a tail at `T₀` therefore transfers to
every `T ≥ T₀`. -/
theorem ratioTail_eventG1_mono_threshold (M : ABKModel d) {s theta c1 T0 T : ℝ}
    (hT0 : 0 ≤ T0) (hT : T0 ≤ T) (n : ℕ)
    (h : (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Support.eventG1 M k s T0)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3)) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Support.eventG1 M k s T)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  refine le_trans (measure_mono ?_) h
  intro omega homega
  simp only [Set.mem_setOf_eq] at homega ⊢
  refine lt_of_lt_of_le homega ?_
  exact scaleProp_mono
    (fun k => Set.compl_subset_compl.2 (Support.eventG1_subset_of_le M k s hT0 hT))
    n omega

/-! ## 5. The closed `𝒢₁` proportion tail -/

/-- **The `𝒢₁` proportion tail with every parameter slot discharged.**

For every model, every `s ∈ (0,1]`, every level `θ` admissible for the
dependence range `r = 1`, and every rate `c₁ ≥ 0`, there is an explicit
threshold `T₀` such that the frozen `𝒢₁(k; s, T)` bad-scale density obeys the
`exp(-c₁n)/3` tail at every `T ≥ T₀` and every window `n`.

This is the `𝒢₁` counterpart of `RatioTailClosed.exists_ratioTail_eventG0`. -/
theorem exists_ratioTail_eventG1 (d : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∀ (M : ABKModel d) (s theta c1 : ℝ), 0 < s → s ≤ 1 → 0 < theta →
        theta * ((r : ℝ) + 1) < 1 → 0 ≤ c1 →
          ∃ T0 : ℝ, 0 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ n : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure
                {omega | theta <
                  scaleProp (fun k => (Support.eventG1 M k s T)ᶜ) n omega}
              ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
  refine ⟨1, le_refl 1, fun M s theta c1 hs0 hs1 htheta0 hthetar hc1 => ?_⟩
  have hlog6 : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hbase : (0 : ℝ) ≤ Real.log 6 + c1 := by linarith only [hlog6, hc1]
  set p : ℝ := 64 * (Real.log 6 + c1) / theta + 2 with hpdef
  have hppos : (0 : ℝ) < p := by
    rw [hpdef]
    have : (0 : ℝ) ≤ 64 * (Real.log 6 + c1) / theta :=
      div_nonneg (by linarith only [hbase]) htheta0.le
    linarith only [this]
  have hp2le : (2 : ℝ) ≤ p := by
    rw [hpdef]
    have : (0 : ℝ) ≤ 64 * (Real.log 6 + c1) / theta :=
      div_nonneg (by linarith only [hbase]) htheta0.le
    linarith only [this]
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp2le]
  set p2 : ℝ := 256 * (Real.log 6 + c1) / (s * theta) + 8 / s + 1 with hp2def
  have hsinv : (1 : ℝ) ≤ 8 / s := by
    rw [le_div_iff₀ hs0]
    linarith only [hs1]
  have hq : (0 : ℝ) ≤ 256 * (Real.log 6 + c1) / (s * theta) :=
    div_nonneg (by linarith only [hbase]) (mul_pos hs0 htheta0).le
  have hp2pos : (0 : ℝ) < p2 := by rw [hp2def]; linarith only [hq, hsinv]
  have hp2one : (1 : ℝ) ≤ p2 := by rw [hp2def]; linarith only [hq, hsinv]
  have hsp2 : (1 : ℝ) ≤ s / 8 * p2 := by
    rw [hp2def, mul_add, mul_add,
      show s / 8 * (256 * (Real.log 6 + c1) / (s * theta))
        = 32 * (Real.log 6 + c1) / theta from by field_simp; ring,
      show s / 8 * (8 / s) = 1 from by field_simp]
    have h1 : (0 : ℝ) ≤ 32 * (Real.log 6 + c1) / theta :=
      div_nonneg (by linarith only [hbase]) htheta0.le
    have h2 : (0 : ℝ) ≤ s / 8 * 1 := by linarith only [hs0]
    linarith only [h1, h2]
  set D : ℝ := gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ * 1 with hDdef
  have hDpos : (0 : ℝ) < D := by
    rw [hDdef, mul_one]
    exact mul_pos (gammaMomentConst_pos (by norm_num)) (Real.rpow_pos_of_pos hppos _)
  set D2 : ℝ := gammaMomentConst 1 * p2 ^ (1 : ℝ)⁻¹ * smallWaveScale d s with hD2def
  have hD2pos : (0 : ℝ) < D2 := by
    rw [hD2def]
    exact mul_pos (mul_pos (gammaMomentConst_pos (by norm_num))
      (Real.rpow_pos_of_pos hp2pos _)) (smallWaveScale_pos d hs0)
  have htheta2 : (0 : ℝ) < theta / 2 := by linarith only [htheta0]
  set Ta : ℝ :=
    D * (9 * ((1 : ℝ) / 2)⁻¹ * Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p)) with hTadef
  set B : ℝ :=
    D2 * (9 * (s / 8)⁻¹ * Cstar ^ (1 / p2) * (theta / 2) ^ (-1 / p2)) with hBdef
  have hBnn : (0 : ℝ) ≤ B :=
    mul_nonneg hD2pos.le
      (appendixD_level_nonneg (by linarith only [hs0] : (0 : ℝ) < s / 8) htheta2)
  have hCpos : (0 : ℝ) < g1bConst s := g1bConst_pos hs0
  set X : ℝ := g1bConst s * B with hXdef
  have hXnn : (0 : ℝ) ≤ X := mul_nonneg hCpos.le hBnn
  have hTsqrt : Real.sqrt X ≤ max Ta (Real.sqrt X) := le_max_right _ _
  have hT0nn : (0 : ℝ) ≤ max Ta (Real.sqrt X) :=
    le_trans (Real.sqrt_nonneg X) hTsqrt
  have hTsq : X ≤ (max Ta (Real.sqrt X)) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg X) hTsqrt 2
    rwa [Real.sq_sqrt hXnn] at h
  have hthetar2 : theta / 2 * (((1 : ℕ) : ℝ) + 1) < 1 := by
    push_cast at hthetar ⊢
    linarith only [hthetar, htheta0]
  have hmain : ∀ n : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure
          {omega | theta <
            scaleProp (fun k =>
              (Support.eventG1 M k s (max Ta (Real.sqrt X)))ᶜ) n omega}
        ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) := by
    intro n
    refine ratioTail_eventG1 M (s := s) (D := D) (D2 := D2) (p := p) (p2 := p2)
      (theta := theta) (c1 := c1) (r := 1)
      hs0 hs1 hDpos hD2pos hp1 hp2one (by linarith only [hp2le]) hsp2 (le_refl 1)
      htheta0 hthetar2 hc1 ?_ ?_ (le_refl D) (le_refl D2) (le_max_left _ _) ?_ n
    · push_cast
      rw [hpdef, show (64 * (Real.log 6 + c1) / theta + 2) = p from hpdef.symm]
      rw [show (1 : ℝ) / 2 * p * (theta / 2) / (16 * 1) = p * theta / 64 from by ring,
        hpdef,
        show (64 * (Real.log 6 + c1) / theta + 2) * theta / 64
          = (Real.log 6 + c1) + theta / 32 from by field_simp; ring]
      have hpos : (0 : ℝ) < theta / 32 := by linarith only [htheta0]
      rw [show (6 : ℝ) * 1 = 6 from by norm_num]
      linarith only [hpos]
    · push_cast
      rw [show s / 8 * p2 * (theta / 2) / (16 * 1) = s * p2 * theta / 256 from by ring,
        hp2def,
        show s * (256 * (Real.log 6 + c1) / (s * theta) + 8 / s + 1) * theta / 256
          = (Real.log 6 + c1) + (8 / s + 1) * s * theta / 256 from by
            field_simp; ring]
      have h2 : (0 : ℝ) < (8 / s + 1) * s * theta / 256 := by positivity
      rw [show (6 : ℝ) * 1 = 6 from by norm_num]
      linarith only [h2]
    · rw [le_div_iff₀ hCpos, mul_comm B (g1bConst s)]
      exact hTsq
  exact ⟨max Ta (Real.sqrt X), hT0nn, fun T hT n =>
    ratioTail_eventG1_mono_threshold M hT0nn hT n (hmain n)⟩

end

end Algsuperdiff.Section4.Provider.Proportion
