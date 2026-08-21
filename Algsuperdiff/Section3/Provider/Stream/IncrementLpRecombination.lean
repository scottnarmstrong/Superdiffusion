import Algsuperdiff.Section3.Provider.Stream.IncrementLpSquared

/-!
# All-`p` squared-norm recombination for stream increments

This file supplies the abstract deterministic/probabilistic recombination left
open by the `p ≥ 2` packaging in `IncrementLpSquared.lean`.  For `p ≥ 1`, set

```
  c(p) := max 1 (2 ^ (2 / p - 1)).
```

Then `1 ≤ c(p) ≤ 2`, and nonnegative `z`, `H`, and `T` with `z ≤ H + T`
satisfy

```
  z ^ (2 / p) ≤ c(p) * (H ^ (2 / p) + T ^ (2 / p)).
```

The wrapper below combines this inequality with the existing
`isBigOWith_gammaSigma_one_rpow_two_div`.  Thus a nonnegative `T =
O_{Γ_{2/p}}(K)` becomes the tail `c(p) T^(2/p) = O_{Γ₁}(c(p) K^(2/p))`.  The
factor multiplies both the deterministic head and the random scale, as
required.

## Scope

This is an **internal abstract provider**, not a claim that `e.kl.bounds.large`
or the corrected all-`p` `e.km.kn.Lp` endpoint is closed.  In particular, it
does not remove the separate general-`p` constant-scope defect: the proved
concentration scale contains `gammaSigmaDescendantsAtScaleConst d 0 (2 / p)`,
which is not bounded here by a dimension-only constant.

## Source

* ABK26, `e.kl.bounds.large`.

## Main declarations

* `streamIncrementLpNormSqSplitConst`: the all-`p` convexity factor.
* `rpow_two_div_le_streamIncrementLpNormSqSplitConst_mul_add`: the scalar
  two-term power inequality.
* `streamIncrementLpNormSq_head_tail_with_splitConst_of_mass_head_tail`: the
  all-`p` abstract `Γ₁` recombination.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open Homogenization
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The all-`p` scalar split -/

/-- The scalar loss for passing from a nonnegative mass bound to the square of
an `L^p` norm.  It equals the subadditive loss `1` when that suffices and the
standard two-term convexity factor otherwise. -/
def streamIncrementLpNormSqSplitConst (p : ℝ) : ℝ :=
  max 1 ((2 : ℝ) ^ (2 / p - 1))

/-- The squared-norm split constant is at least one. -/
theorem one_le_streamIncrementLpNormSqSplitConst (p : ℝ) :
    1 ≤ streamIncrementLpNormSqSplitConst p :=
  le_max_left _ _

/-- The squared-norm split constant is positive. -/
theorem streamIncrementLpNormSqSplitConst_pos (p : ℝ) :
    0 < streamIncrementLpNormSqSplitConst p :=
  lt_of_lt_of_le zero_lt_one (one_le_streamIncrementLpNormSqSplitConst p)

/-- For the source range `p ≥ 1`, the squared-norm split costs at most two. -/
theorem streamIncrementLpNormSqSplitConst_le_two {p : ℝ} (hp : 1 ≤ p) :
    streamIncrementLpNormSqSplitConst p ≤ 2 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hq2 : 2 / p ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hp0]
    nlinarith
  have hexp : 2 / p - 1 ≤ (1 : ℝ) := by linarith
  rw [streamIncrementLpNormSqSplitConst]
  refine max_le (by norm_num) ?_
  calc
    (2 : ℝ) ^ (2 / p - 1) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 := Real.rpow_one 2

/-- The all-`p` two-term real-power inequality.  For `2 / p ≤ 1` this is
subadditivity; otherwise it is Mathlib's two-point convex mean inequality. -/
theorem rpow_two_div_le_streamIncrementLpNormSqSplitConst_mul_add
    {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (2 / p) ≤
      streamIncrementLpNormSqSplitConst p * (a ^ (2 / p) + b ^ (2 / p)) := by
  by_cases hq : 2 / p ≤ 1
  · calc
      (a + b) ^ (2 / p) ≤ a ^ (2 / p) + b ^ (2 / p) :=
        Real.rpow_add_le_add_rpow ha hb (by positivity) hq
      _ ≤ streamIncrementLpNormSqSplitConst p *
          (a ^ (2 / p) + b ^ (2 / p)) := by
        apply le_mul_of_one_le_left
        · exact add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)
        · exact one_le_streamIncrementLpNormSqSplitConst p
  · have hq1 : (1 : ℝ) ≤ 2 / p := le_of_not_ge hq
    have hconv :
        (a + b) ^ (2 / p) ≤
          (2 : ℝ) ^ (2 / p - 1) * (a ^ (2 / p) + b ^ (2 / p)) := by
      let a' : NNReal := ⟨a, ha⟩
      let b' : NNReal := ⟨b, hb⟩
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a' b' hq1
    calc
      (a + b) ^ (2 / p) ≤
          (2 : ℝ) ^ (2 / p - 1) * (a ^ (2 / p) + b ^ (2 / p)) := hconv
      _ ≤ streamIncrementLpNormSqSplitConst p *
          (a ^ (2 / p) + b ^ (2 / p)) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_max_right _ _
        · exact add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)

/-! ## Abstract stream-increment recombination -/

/-- An all-`p` squared-norm head/tail package.  If a nonnegative stream
increment mass is bounded by a deterministic head `H` plus a nonnegative
`O_{Γ_{2/p}}(K)` tail `T`, then its squared `L^p` norm is bounded by the
split constant times both powered terms, and the scaled powered tail is
`O_{Γ₁}` at the correspondingly scaled amplitude. -/
theorem streamIncrementLpNormSq_head_tail_with_splitConst_of_mass_head_tail
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (l n m : ℤ) {H K : ℝ}
    {T : ShellSeq d → ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hT_nonneg : ∀ omega, 0 ≤ T omega)
    (hmass : ∀ omega, streamIncrementLpMass p l n m omega ≤ H + T omega)
    (hT : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma (2 / p)) T K) :
    let c := streamIncrementLpNormSqSplitConst p
    (∀ omega : ShellSeq d, 0 ≤ c * T omega ^ (2 / p)) ∧
      (∀ omega : ShellSeq d,
        streamIncrementLpNorm p l n m omega ^ 2 ≤
          c * H ^ (2 / p) + c * T omega ^ (2 / p)) ∧
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
        (fun omega : ShellSeq d => c * T omega ^ (2 / p))
        (c * K ^ (2 / p)) := by
  dsimp only
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hc : 0 ≤ streamIncrementLpNormSqSplitConst p :=
    (streamIncrementLpNormSqSplitConst_pos p).le
  refine ⟨fun omega => mul_nonneg hc (Real.rpow_nonneg (hT_nonneg omega) _), ?_, ?_⟩
  · intro omega
    rw [streamIncrementLpNorm_sq_eq_mass_rpow, ← mul_add]
    calc
      streamIncrementLpMass p l n m omega ^ (2 / p) ≤
          (H + T omega) ^ (2 / p) :=
        Real.rpow_le_rpow (streamIncrementLpMass_nonneg p l n m omega)
          (hmass omega) (by positivity)
      _ ≤ streamIncrementLpNormSqSplitConst p *
          (H ^ (2 / p) + T omega ^ (2 / p)) :=
        rpow_two_div_le_streamIncrementLpNormSqSplitConst_mul_add hp0 hH
          (hT_nonneg omega)
  · exact IndependentSums.IsBigOWith.const_mul hc
      (isBigOWith_gammaSigma_one_rpow_two_div hp0 hK hT_nonneg hT)

end

end Algsuperdiff.Section3.Provider.Stream
