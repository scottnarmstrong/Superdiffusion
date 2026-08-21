import Algsuperdiff.Section4.Probability.ScalesConcentration.Statement

/-!
# Carrier-neutral indicator-density layer for the Appendix-D concentration output

ABK26, §4.1.  This module is the abstract-`Ω` bridge between Proposition
`p.concentration.for.scales`
(`Algsuperdiff.Section4.Probability.ScalesConcentration.Statement`) and the
"proportion of good scales" statements of §4.1: it defines the Cesàro density of
the scales at which a family of events holds, and proves the three purely
measure-theoretic facts that every §4.1 ratio lemma consumes.

## Contents

* `scaleProp Ev M ω` — the proportion of scales `m ∈ {0,…,M}` at which `Ev m`
  holds.  With `Ev` the good event this is the paper's `avsum 𝟙{𝒢(m;s,ε)}`;
  with `Ev = (𝒢ᵢ ·)ᶜ` it is the density of *bad* scales.
* `badProp_bound_of_concentration` — the measure-theoretic core: given the
  conclusion of `p_concentration_for_scales` for an array `X` together with the
  deterministic reduction embedding each bad event into the concentration
  threshold event, the bad-scale density obeys the same exponential tail.
* `scaleProp_inter_le` / `setOf_scaleProp_inter_subset` — the two-fold split
  (the paper's "apply `p.concentration.for.scales` twice at level `½θ`").
* `scaleProp_subadd` / `measure_bad_density_union` — the three-fold union bound
  behind `p.independence.between.scales` (the paper's "`θ` replaced by
  `θ/3`").

## Orientation of the conclusions (complementarity note)

Pointwise `𝟙{ω ∈ Ev m} + 𝟙{ω ∈ (Ev m)ᶜ} = 1`, so over the `M+1` scales
`scaleProp Ev M ω + scaleProp (·ᶜ) M ω = 1`.  Hence the paper's good-proportion
clause `avsum 𝟙{𝒢} ≤ 1 − θ` and the bad-proportion clause
`θ < avsum 𝟙{𝒢ᶜ}` — the form concentration natively delivers — are
complementary.  Every conclusion below is phrased in the bad-proportion form.
This is recorded as a note, not as a lemma.

## Scope

Provider material: carrier-neutral local helpers over an abstract probability
space, with no ABK carrier and no model.  They are conditional A: the
concentration output and the deterministic reduction enter as hypotheses.  No
`sorry`, no custom axioms, no `set_option maxHeartbeats`.
-/

open MeasureTheory
open Algsuperdiff.Section4.Probability.ScalesConcentration
open scoped ENNReal

namespace Algsuperdiff.Section4.Probability.IndicatorDensity

variable {Ω : Type*}

/-! ### The proportion of good / bad scales over a window `{0,…,M}` -/

open scoped Classical in
/-- The (Cesàro) **proportion of scales `m ∈ {0,…,M}` at which `Ev m` holds**,
`avsum_{m=0}^M 𝟙{ω ∈ Ev m}`.  With `Ev` the good event this is the paper's
`avsum 𝟙{𝒢(m;s,ε)}`; with `Ev = (𝒢ᵢ ·)ᶜ` it is the density of bad scales. -/
noncomputable def scaleProp (Ev : ℤ → Set Ω) (M : ℕ) (ω : Ω) : ℝ :=
  (1 / ((M : ℝ) + 1)) *
    ∑ m ∈ Finset.Icc (0 : ℤ) (M : ℤ), (if ω ∈ Ev m then (1 : ℝ) else 0)

/-! ### The measure-theoretic core of every ratio lemma -/

/-- **The measure-theoretic core of every ratio lemma.**  Given the concentration
output `hconc` for an array `X` (the conclusion of `p_concentration_for_scales`
with its universal constant `C` extracted) and the deterministic reduction
`hreduce` embedding each bad event `(Ev m)ᶜ` into the concentration threshold
event, the density of bad scales `scaleProp (·ᶜ)` obeys the same exponential
tail.  Pure `measure_mono` over an indicator-sum domination. -/
theorem badProp_bound_of_concentration [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℤ → ℤ → Ω → ℝ) {p s : ℝ} {r : ℕ} (C : ℝ)
    (hconc : ∀ (m : ℕ) (θ : ℝ), (r : ℤ) ≤ (m : ℤ) → 0 < θ → θ ≤ 1 →
      P {ω | θ < (1 / ((m : ℝ) + 1)) *
          ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 9 * s⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
              then (1 : ℝ) else 0)}
        ≤ ENNReal.ofReal (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1))))
    (Ev : ℤ → Set Ω) (M : ℕ) (θ : ℝ) (hrM : (r : ℤ) ≤ (M : ℤ)) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hreduce : ∀ m ∈ Finset.Icc (0 : ℤ) (M : ℤ), ∀ ω ∈ (Ev m)ᶜ,
        9 * s⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s m ω) :
    P {ω | θ < scaleProp (fun m => (Ev m)ᶜ) M ω}
      ≤ ENNReal.ofReal (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((M : ℝ) + 1))) := by
  classical
  refine le_trans (measure_mono ?_) (hconc M θ hrM hθ0 hθ1)
  intro ω hω
  simp only [Set.mem_setOf_eq, scaleProp] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  have hnn : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m hm => ?_)) hnn
  by_cases hmem : ω ∈ (Ev m)ᶜ
  · simp only [if_pos hmem, if_pos (hreduce m hm ω hmem), le_refl]
  · rw [if_neg hmem]; split_ifs <;> norm_num

/-! ### The two-fold split: `p.concentration.for.scales` applied twice at `½θ` -/

/-- **Two-fold subadditivity of the bad-scale density.**  Pointwise
`𝟙{(A∩B)ᶜ} ≤ 𝟙{Aᶜ} + 𝟙{Bᶜ}`; averaging over the window keeps it. -/
theorem scaleProp_inter_le (A B : ℤ → Set Ω) (M : ℕ) (ω : Ω) :
    scaleProp (fun m => (A m ∩ B m)ᶜ) M ω
      ≤ scaleProp (fun m => (A m)ᶜ) M ω + scaleProp (fun m => (B m)ᶜ) M ω := by
  simp only [scaleProp]
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ => ?_)) (by positivity)
  by_cases hAB : ω ∈ (A m ∩ B m)ᶜ
  · rw [if_pos hAB]
    have hmem : ω ∉ A m ∨ ω ∉ B m := by
      by_contra hc
      push_neg at hc
      exact hAB ⟨hc.1, hc.2⟩
    rcases hmem with hc | hc
    · rw [if_pos ((Set.mem_compl_iff _ _).mpr hc)]; split_ifs <;> norm_num
    · rw [if_pos ((Set.mem_compl_iff _ _).mpr hc)]; split_ifs <;> norm_num
  · rw [if_neg hAB]; split_ifs <;> norm_num

/-- **The `½θ` split, as an inclusion of events.**  A `θ`-density of `(A ∩ B)`-bad
scales forces a `θ₁`-density for `A` or a `θ₂`-density for `B`, whenever
`θ₁ + θ₂ ≤ θ`.

This is the Lean form of the paper's own bookkeeping in
`l.ratio.of.good.scales.for.k`: are **two separate applications** of
`p.concentration.for.scales`, each at level `½θ`, combined at the end of Step -/
theorem setOf_scaleProp_inter_subset (A B : ℤ → Set Ω) (M : ℕ) {θ θ₁ θ₂ : ℝ}
    (hθ : θ₁ + θ₂ ≤ θ) :
    {ω | θ < scaleProp (fun m => (A m ∩ B m)ᶜ) M ω}
      ⊆ {ω | θ₁ < scaleProp (fun m => (A m)ᶜ) M ω}
        ∪ {ω | θ₂ < scaleProp (fun m => (B m)ᶜ) M ω} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hc
  linarith [scaleProp_inter_le A B M ω, hc.1, hc.2]

/-! ### The three-fold union bound -/

/-- **Bad-scale density is subadditive under intersection.**  With
`𝒢 = A ∩ B ∩ C`, the density of scales at which `𝒢` fails is at most the sum of
the densities at which each factor fails.  Pointwise
`𝟙{(A∩B∩C)ᶜ} ≤ 𝟙{Aᶜ} + 𝟙{Bᶜ} + 𝟙{Cᶜ}`. -/
theorem scaleProp_subadd (A B Cev : ℤ → Set Ω) (M : ℕ) (ω : Ω) :
    scaleProp (fun m => (A m ∩ B m ∩ Cev m)ᶜ) M ω
      ≤ scaleProp (fun m => (A m)ᶜ) M ω + scaleProp (fun m => (B m)ᶜ) M ω
          + scaleProp (fun m => (Cev m)ᶜ) M ω := by
  simp only [scaleProp]
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ => ?_)) (by positivity)
  by_cases hABC : ω ∈ (A m ∩ B m ∩ Cev m)ᶜ
  · rw [if_pos hABC]
    have hmem : ω ∉ A m ∨ ω ∉ B m ∨ ω ∉ Cev m := by
      by_contra hc; push_neg at hc
      exact hABC ⟨⟨hc.1, hc.2.1⟩, hc.2.2⟩
    rcases hmem with h | h | h
    · rw [if_pos ((Set.mem_compl_iff _ _).mpr h)]; split_ifs <;> norm_num
    · rw [if_pos ((Set.mem_compl_iff _ _).mpr h)]; split_ifs <;> norm_num
    · rw [if_pos ((Set.mem_compl_iff _ _).mpr h)]; split_ifs <;> norm_num
  · rw [if_neg hABC]; split_ifs <;> norm_num

/-- **The measure union bound over three bad-scale densities.**  Given the three
ratio-lemma tails at level `θ/3` and the subadditivity `scaleProp_subadd`, the
density of scales at which `A ∩ B ∩ C` fails exceeds `θ` with probability at most
`e₀ + e₁ + e₂`. -/
theorem measure_bad_density_union [MeasurableSpace Ω] (P : Measure Ω)
    (A B Cev : ℤ → Set Ω) (M : ℕ) (θ e₀ e₁ e₂ : ℝ)
    (hA : P {ω | θ / 3 < scaleProp (fun m => (A m)ᶜ) M ω} ≤ ENNReal.ofReal e₀)
    (hB : P {ω | θ / 3 < scaleProp (fun m => (B m)ᶜ) M ω} ≤ ENNReal.ofReal e₁)
    (hC : P {ω | θ / 3 < scaleProp (fun m => (Cev m)ᶜ) M ω} ≤ ENNReal.ofReal e₂) :
    P {ω | θ < scaleProp (fun m => (A m ∩ B m ∩ Cev m)ᶜ) M ω}
      ≤ ENNReal.ofReal e₀ + ENNReal.ofReal e₁ + ENNReal.ofReal e₂ := by
  have hsub : {ω | θ < scaleProp (fun m => (A m ∩ B m ∩ Cev m)ᶜ) M ω}
      ⊆ {ω | θ / 3 < scaleProp (fun m => (A m)ᶜ) M ω}
        ∪ {ω | θ / 3 < scaleProp (fun m => (B m)ᶜ) M ω}
        ∪ {ω | θ / 3 < scaleProp (fun m => (Cev m)ᶜ) M ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hle := scaleProp_subadd A B Cev M ω
    have hsum : θ < scaleProp (fun m => (A m)ᶜ) M ω + scaleProp (fun m => (B m)ᶜ) M ω
        + scaleProp (fun m => (Cev m)ᶜ) M ω := lt_of_lt_of_le hω hle
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hc
    linarith [hc.1.1, hc.1.2, hc.2]
  calc P {ω | θ < scaleProp (fun m => (A m ∩ B m ∩ Cev m)ᶜ) M ω}
      ≤ P ({ω | θ / 3 < scaleProp (fun m => (A m)ᶜ) M ω}
          ∪ {ω | θ / 3 < scaleProp (fun m => (B m)ᶜ) M ω}
          ∪ {ω | θ / 3 < scaleProp (fun m => (Cev m)ᶜ) M ω}) := measure_mono hsub
    _ ≤ P ({ω | θ / 3 < scaleProp (fun m => (A m)ᶜ) M ω}
          ∪ {ω | θ / 3 < scaleProp (fun m => (B m)ᶜ) M ω})
          + P {ω | θ / 3 < scaleProp (fun m => (Cev m)ᶜ) M ω} := measure_union_le _ _
    _ ≤ (P {ω | θ / 3 < scaleProp (fun m => (A m)ᶜ) M ω}
          + P {ω | θ / 3 < scaleProp (fun m => (B m)ᶜ) M ω})
          + P {ω | θ / 3 < scaleProp (fun m => (Cev m)ᶜ) M ω} :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal e₀ + ENNReal.ofReal e₁ + ENNReal.ofReal e₂ :=
        add_le_add (add_le_add hA hB) hC

end Algsuperdiff.Section4.Probability.IndicatorDensity
