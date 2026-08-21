/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Support.Events
import Algsuperdiff.Section4.Probability.IndicatorDensity

/-!
# The three-lane interface of the `§4.1` proportion assembly

ABK26, §4.1, `p.independence.between.scales`.  The proof of that proposition
splits `𝟙{𝒢(m; s, ε)ᶜ}` into the three constituent complements and applies each
lane's ratio lemma "with `θ` replaced by `θ/3`".  This module is the *interface*
of that step:

* `LaneTail M Ev θ c₁` — the common endpoint shape of one lane: at **every**
  window `{0,…,n}` the density of scales at which `Ev` fails exceeds `θ` with
  probability at most `exp(−c₁n)/3`.  It is exactly the conclusion shape the
  `𝒢₀` lane (`RatioTailClosed`/`RatioTailUniform`) and the `𝒢₁` lane
  (`G1RatioTail`/`G1ThresholdArith`) deliver.
* `measure_scaleProp_compl_goodEventBase_le` — the three-fold union bound:
  three `LaneTail`s at level `θ/3` give the `θ`-level tail of the *intersection*
  `goodEventBase`, at prefactor `1`.

The `𝒢₂` lane enters here **only** as a named hypothesis of type `LaneTail M
(fun k => Support.eventG2 M k s ε) (θ/3) c₁`.

## References

* ABK26, `p.independence.between.scales`; `d.good.event.for.lambda`,
  (`e.lambda.good.events`).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The common lane endpoint -/

/-- **The shape of one lane's ratio-tail endpoint.**  `LaneTail M Ev θ c₁` says
that for every window `{0,…,n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not itself reach (covered inside the proved
`ratioTail_of_concentration`) — the density of scales at which `Ev` fails
exceeds `θ` with probability at most `exp(−c₁n)/3`.

The prefactor `1/3` is the union-bound share of the three-lane split: three
lanes at `exp(−c₁n)/3` recombine to `exp(−c₁n)`. -/
def LaneTail (M : ABKModel d) (Ev : ℤ → Set (Cutoff.CutoffSample d))
    (theta c1 : ℝ) : Prop :=
  ∀ n : ℕ,
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev k)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3)

/-- A lane endpoint transfers to every larger level: the bad-density event
shrinks as the level rises. -/
theorem LaneTail.mono_level {M : ABKModel d} {Ev : ℤ → Set (Cutoff.CutoffSample d)}
    {theta theta' c1 : ℝ} (h : theta ≤ theta') (H : LaneTail M Ev theta c1) :
    LaneTail M Ev theta' c1 := by
  intro n
  refine le_trans (measure_mono ?_) (H n)
  intro omega homega
  exact lt_of_le_of_lt h homega

/-- A lane endpoint transfers to every smaller rate: `exp(−c₁n)` grows as `c₁`
falls. -/
theorem LaneTail.mono_rate {M : ABKModel d} {Ev : ℤ → Set (Cutoff.CutoffSample d)}
    {theta c1 c1' : ℝ} (h : c1' ≤ c1) (H : LaneTail M Ev theta c1) :
    LaneTail M Ev theta c1' := by
  intro n
  refine le_trans (H n) (ENNReal.ofReal_le_ofReal ?_)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : Real.exp (-c1 * (n : ℝ)) ≤ Real.exp (-c1' * (n : ℝ)) := by
    refine Real.exp_le_exp.2 ?_
    have hstep : -c1 * (n : ℝ) ≤ -c1' * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [h]) hn
    exact hstep
  linarith only [hexp]

/-- A lane endpoint transfers along an inclusion of the good events. -/
theorem LaneTail.mono_event {M : ABKModel d} {Ev Ev' : ℤ → Set (Cutoff.CutoffSample d)}
    {theta c1 : ℝ} (h : ∀ k, Ev k ⊆ Ev' k) (H : LaneTail M Ev theta c1) :
    LaneTail M Ev' theta c1 := by
  intro n
  refine le_trans (measure_mono ?_) (H n)
  intro omega homega
  simp only [Set.mem_setOf_eq] at homega ⊢
  refine lt_of_lt_of_le homega ?_
  classical
  simp only [scaleProp]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
  by_cases hm : omega ∈ (Ev' m)ᶜ
  · rw [if_pos hm, if_pos (Set.compl_subset_compl.2 (h m) hm)]
  · rw [if_neg hm]
    split_ifs <;> norm_num

/-! ## 2. The three-fold union bound -/

/-- **The three lanes recombine into the good event.**  With the three lane
endpoints at level `θ/3` — `𝒢₀`, `𝒢₁` at the substituted threshold
`s ε √c⋆ (√γ)⁻¹` of `e.lambda.good.events`, and `𝒢₂` — the density of scales at
which the frozen good event's untranslated body `goodEventBase` fails exceeds
`θ` with probability at most `exp(−c₁n)`, at every window `n`. -/
theorem measure_scaleProp_compl_goodEventBase_le (M : ABKModel d) (Ccg : ℝ)
    (s : {s : ℝ // 0 < s}) (ep theta c1 : ℝ)
    (h0 : LaneTail M (fun k => Support.eventG0 M Ccg k) (theta / 3) c1)
    (h1 : LaneTail M
      (fun k => Support.eventG1 M k (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (theta / 3) c1)
    (h2 : LaneTail M (fun k => Support.eventG2 M k s ep) (theta / 3) c1)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta <
          scaleProp (fun k => (Support.goodEventBase M Ccg k s ep)ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
  have hbase : ∀ k : ℤ, Support.goodEventBase M Ccg k s ep =
      Support.eventG0 M Ccg k ∩
        Support.eventG1 M k (s : ℝ)
          ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ∩
        Support.eventG2 M k s ep := fun _ => rfl
  have hunion := measure_bad_density_union (Cutoff.cutoffSampleLaw M).toMeasure
    (fun k => Support.eventG0 M Ccg k)
    (fun k => Support.eventG1 M k (s : ℝ)
      ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (fun k => Support.eventG2 M k s ep) n theta
    (Real.exp (-c1 * (n : ℝ)) / 3) (Real.exp (-c1 * (n : ℝ)) / 3)
    (Real.exp (-c1 * (n : ℝ)) / 3) (h0 n) (h1 n) (h2 n)
  have hnn : (0 : ℝ) ≤ Real.exp (-c1 * (n : ℝ)) / 3 := by positivity
  have hsum : ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3)
      = ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
    rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_add (by linarith only [hnn]) hnn]
    congr 1
    ring
  rw [hsum] at hunion
  simp only [hbase]
  exact hunion

/-! ## 3. The good-proportion form

`IndicatorDensity` records the complementarity `avsum 𝟙{𝒢} + avsum 𝟙{𝒢ᶜ} = 1` as a
note rather than a lemma.  The frozen proportion display is stated in the *good*
form `avsum 𝟙{𝒢} ≤ 1 − θ`, which is the NON-strict complement of the bad form the
lanes deliver, so the conversion costs one strict inequality: the lanes are run at
`θ/4` instead of `θ/3`. -/

/-- **The good and bad scale densities are complementary.** -/
theorem scaleProp_add_scaleProp_compl {Omega : Type*} (Ev : ℤ → Set Omega) (n : ℕ)
    (omega : Omega) :
    scaleProp Ev n omega + scaleProp (fun m => (Ev m)ᶜ) n omega = 1 := by
  simp only [scaleProp]
  rw [← mul_add, ← Finset.sum_add_distrib]
  have key : (1 : ℝ) / ((n : ℝ) + 1) * (∑ _m ∈ Finset.Icc (0 : ℤ) (n : ℤ), (1 : ℝ)) = 1 := by
    rw [Finset.sum_const, Int.card_Icc]
    have h : ((n : ℤ) + 1 - 0).toNat = n + 1 := by omega
    rw [h]
    simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    field_simp
  refine Eq.trans ?_ key
  refine congrArg (fun z : ℝ => (1 : ℝ) / ((n : ℝ) + 1) * z) ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : omega ∈ Ev m
  · rw [if_pos h, if_neg (fun hc => hc h)]
    norm_num
  · rw [if_neg h, if_pos (show omega ∈ (Ev m)ᶜ from h)]
    norm_num

/-- **The good-proportion form of the three-lane union bound.**  With the three
lane endpoints at level `θ/4`, the frozen display's own clause
`avsum 𝟙{𝒢} ≤ 1 − θ` has probability at most `exp(−c₁n)`, at every window `n`. -/
theorem measure_scaleProp_goodEventBase_le (M : ABKModel d) (Ccg : ℝ)
    (s : {s : ℝ // 0 < s}) (ep theta c1 : ℝ) (htheta0 : 0 < theta)
    (h0 : LaneTail M (fun k => Support.eventG0 M Ccg k) (theta / 4) c1)
    (h1 : LaneTail M
      (fun k => Support.eventG1 M k (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (theta / 4) c1)
    (h2 : LaneTail M (fun k => Support.eventG2 M k s ep) (theta / 4) c1)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | scaleProp (fun k => Support.goodEventBase M Ccg k s ep) n omega
          ≤ 1 - theta}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
  have hbase : ∀ k : ℤ, Support.goodEventBase M Ccg k s ep =
      Support.eventG0 M Ccg k ∩
        Support.eventG1 M k (s : ℝ)
          ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ∩
        Support.eventG2 M k s ep := fun _ => rfl
  have hsub : {omega | scaleProp (fun k => Support.goodEventBase M Ccg k s ep) n omega
        ≤ 1 - theta}
      ⊆ {omega | theta / 4 < scaleProp (fun k => (Support.eventG0 M Ccg k)ᶜ) n omega}
        ∪ {omega | theta / 4 < scaleProp (fun k =>
            (Support.eventG1 M k (s : ℝ)
              ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))ᶜ) n omega}
        ∪ {omega | theta / 4 < scaleProp (fun k => (Support.eventG2 M k s ep)ᶜ) n omega} := by
    intro omega homega
    simp only [Set.mem_setOf_eq] at homega
    have hcompl := scaleProp_add_scaleProp_compl
      (fun k => Support.goodEventBase M Ccg k s ep) n omega
    have hbad : theta ≤ scaleProp
        (fun k => (Support.goodEventBase M Ccg k s ep)ᶜ) n omega := by
      linarith only [hcompl, homega]
    have hsplit := scaleProp_subadd (fun k => Support.eventG0 M Ccg k)
      (fun k => Support.eventG1 M k (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
      (fun k => Support.eventG2 M k s ep) n omega
    simp only [← hbase] at hsplit
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hc
    linarith only [htheta0, hbad, hsplit, hc.1.1, hc.1.2, hc.2]
  have hnn : (0 : ℝ) ≤ Real.exp (-c1 * (n : ℝ)) / 3 := by positivity
  have hsum : ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
      ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3)
      = ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := by
    rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_add (by linarith only [hnn]) hnn]
    congr 1
    ring
  calc (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | scaleProp (fun k => Support.goodEventBase M Ccg k s ep) n omega ≤ 1 - theta}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
          ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) +
          ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / 3) :=
        add_le_add (add_le_add (h0 n) (h1 n)) (h2 n)
    _ = ENNReal.ofReal (Real.exp (-c1 * (n : ℝ))) := hsum

end

end Algsuperdiff.Section4.Provider.Proportion
