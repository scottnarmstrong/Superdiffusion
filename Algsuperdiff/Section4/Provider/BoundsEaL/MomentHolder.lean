/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.BoundsEaL.MomentEngine

/-!
# Step 5's Hölder bookkeeping, in the anchor's `lintegral` normal form

## What this module supplies

Step 5 of the proof of `l.bounds.mathcal.E.aL` reads:

> Using these estimates, the restrictions `m − n ≤ γ^{-1}` and
> `p ≤ C^{-1}γ^{-1}s` and **Hölder's inequality**, it is straightforward to see
> that the `p`-th root of the sum over `j ≤ n` of the `p/2`-th moment of the
> first and third terms ... is bounded by the right side.

Each term of `e.apply.sensitivity.J.aL` is a PRODUCT of the Step-4 bullets, and
each bullet is available at EVERY moment `q ∈ [1,∞)` (that is exactly what the
`hence, for every q` sentences of Step 4 deliver).
Hölder therefore costs nothing except a uniform boost of the exponent by the
number of factors.

* `lintegral_rpow_prod_le_of_moments` — an `N`-factor product whose factors
  each obey the normal form at the boosted exponent `N q` obeys it at `q`, with
  the product of the majorants.  This is the reconstruction of the source's
  "Hölder's inequality" for the four terms.
* `lintegral_rpow_mul_le_of_moments` — the two-factor instance, spelled out.
* `lintegral_rpow_sum_le_of_moments` — the companion `ℝ≥0∞` Minkowski step for a
  finite SUM of terms (the three summands of `e.apply.sensitivity.J.aL`, and the
  primal/adjoint pair of `lFreeStep3Majorant`), at `q ≥ 1`.

Both engines are exponent-neutral: no `γ`-power and no `s`-power is moved, and
no constant beyond the product/sum of the caller's own majorants is introduced.

## References

* Mathlib: `ENNReal.lintegral_prod_norm_pow_le`, `ENNReal.lintegral_Lp_add_le`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {ι : Type*}

/-! ## 1. Two `ℝ≥0∞` product identities -/

/-- A nonnegative `ℝ≥0∞` power distributes over a finite product. -/
private theorem prodRpowOfNonneg (t : Finset ι) (f : ι → ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) :
    (∏ i ∈ t, f i) ^ z = ∏ i ∈ t, (f i) ^ z := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, ENNReal.one_rpow]
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        ENNReal.mul_rpow_of_nonneg _ _ hz, ih]

/-! ## 2. Hölder for a finite product, in the anchor's normal form -/

/-- **The Step-5 Hölder step.**

If `N = t.card` observables each satisfy the development normal form `∫⁻ (X
i)^{N q} ≤ (ofReal (R i))^{N q}` at the boosted exponent `N q`, then their
product satisfies it at `q`, with the product of the majorants:

```
∫⁻ ( Π_{i ∈ t} X i )^q  ≤  ( ofReal ( Π_{i ∈ t} R i ) )^q .
```

This is exactly how the source uses Hölder in Step 5: every Step-4 bullet is
available at every moment, so raising the exponent by the (fixed, small) number
of factors is free, and no constant is spent. -/
theorem lintegral_rpow_prod_le_of_moments {mu : Measure Omega} (t : Finset ι)
    (ht : t.Nonempty) {X : ι → Omega → ℝ≥0∞} {R : ι → ℝ} {q : ℝ} (hq : 0 < q)
    (hXm : ∀ i ∈ t, AEMeasurable (X i) mu) (hR : ∀ i ∈ t, 0 ≤ R i)
    (hmom : ∀ i ∈ t, (∫⁻ omega, X i omega ^ (((t.card : ℕ) : ℝ) * q) ∂mu) ≤
      ENNReal.ofReal (R i) ^ (((t.card : ℕ) : ℝ) * q)) :
    (∫⁻ omega, (∏ i ∈ t, X i omega) ^ q ∂mu) ≤ ENNReal.ofReal (∏ i ∈ t, R i) ^ q := by
  classical
  have hcard : 0 < t.card := Finset.card_pos.mpr ht
  have hN0 : (0 : ℝ) < ((t.card : ℕ) : ℝ) := by exact_mod_cast hcard
  have hNne : ((t.card : ℕ) : ℝ) ≠ 0 := ne_of_gt hN0
  have hNinv : (0 : ℝ) ≤ (((t.card : ℕ) : ℝ))⁻¹ := (inv_pos.mpr hN0).le
  -- the integrand, rewritten as a Hölder product
  have hint : ∀ omega : Omega, (∏ i ∈ t, X i omega) ^ q =
      ∏ i ∈ t, (X i omega ^ (((t.card : ℕ) : ℝ) * q)) ^ ((((t.card : ℕ) : ℝ))⁻¹) := by
    intro omega
    rw [prodRpowOfNonneg t _ hq.le]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  -- the exponents sum to one
  have hsumexp : (∑ _i ∈ t, (((t.card : ℕ) : ℝ))⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  -- Mathlib's multi-argument Hölder
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := mu) t
    (f := fun i omega => X i omega ^ (((t.card : ℕ) : ℝ) * q))
    (fun i hi => (hXm i hi).pow_const _)
    (p := fun _ => (((t.card : ℕ) : ℝ))⁻¹) hsumexp (fun _ _ => hNinv)
  -- the per-factor moment inputs
  have hfactor : ∀ i ∈ t, (∫⁻ omega, X i omega ^ (((t.card : ℕ) : ℝ) * q) ∂mu) ^
      ((((t.card : ℕ) : ℝ))⁻¹) ≤ ENNReal.ofReal (R i) ^ q := by
    intro i hi
    refine le_trans (ENNReal.rpow_le_rpow (hmom i hi) hNinv) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  calc (∫⁻ omega, (∏ i ∈ t, X i omega) ^ q ∂mu)
      = ∫⁻ omega, ∏ i ∈ t,
          (X i omega ^ (((t.card : ℕ) : ℝ) * q)) ^ ((((t.card : ℕ) : ℝ))⁻¹) ∂mu :=
        lintegral_congr hint
    _ ≤ ∏ i ∈ t, (∫⁻ omega, X i omega ^ (((t.card : ℕ) : ℝ) * q) ∂mu) ^
          ((((t.card : ℕ) : ℝ))⁻¹) := hholder
    _ ≤ ∏ i ∈ t, ENNReal.ofReal (R i) ^ q := Finset.prod_le_prod' hfactor
    _ = ENNReal.ofReal (∏ i ∈ t, R i) ^ q := by
        rw [ENNReal.ofReal_prod_of_nonneg hR, prodRpowOfNonneg t _ hq.le]

/-- **The two-factor Hölder step**, spelled out: a product of two observables,
each controlled at the doubled exponent `2q`. -/
theorem lintegral_rpow_mul_le_of_moments {mu : Measure Omega} {X Y : Omega → ℝ≥0∞}
    {RX RY q : ℝ} (hq : 0 < q) (hXm : AEMeasurable X mu) (hYm : AEMeasurable Y mu)
    (hRX : 0 ≤ RX)
    (hX : (∫⁻ omega, X omega ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RX ^ (2 * q))
    (hY : (∫⁻ omega, Y omega ^ (2 * q) ∂mu) ≤ ENNReal.ofReal RY ^ (2 * q)) :
    (∫⁻ omega, (X omega * Y omega) ^ q ∂mu) ≤ ENNReal.ofReal (RX * RY) ^ q := by
  have h2q : (0 : ℝ) < 2 * q := by linarith only [hq]
  have hint : ∀ omega : Omega, (X omega * Y omega) ^ q =
      (X omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) * (Y omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) := by
    intro omega
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 1 <;> congr 1 <;> ring
  have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := mu)
    (f := fun omega => X omega ^ (2 * q)) (g := fun omega => Y omega ^ (2 * q))
    (hXm.pow_const _) (hYm.pow_const _) (p := (2 : ℝ)⁻¹) (q := (2 : ℝ)⁻¹)
    (by norm_num) (by norm_num) (by norm_num)
  have hstepX : (∫⁻ omega, X omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) ≤ ENNReal.ofReal RX ^ q := by
    refine le_trans (ENNReal.rpow_le_rpow hX (by norm_num)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hstepY : (∫⁻ omega, Y omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) ≤ ENNReal.ofReal RY ^ q := by
    refine le_trans (ENNReal.rpow_le_rpow hY (by norm_num)) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  calc (∫⁻ omega, (X omega * Y omega) ^ q ∂mu)
      = ∫⁻ omega, (X omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) *
          (Y omega ^ (2 * q)) ^ ((2 : ℝ)⁻¹) ∂mu := lintegral_congr hint
    _ ≤ (∫⁻ omega, X omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) *
          (∫⁻ omega, Y omega ^ (2 * q) ∂mu) ^ ((2 : ℝ)⁻¹) := hholder
    _ ≤ ENNReal.ofReal RX ^ q * ENNReal.ofReal RY ^ q :=
        mul_le_mul' hstepX hstepY
    _ = ENNReal.ofReal (RX * RY) ^ q := by
        rw [ENNReal.ofReal_mul hRX, ENNReal.mul_rpow_of_nonneg _ _ hq.le]

/-! ## 3. The companion Minkowski step for a finite sum -/

/-- **The Step-5 Minkowski step.**

A finite sum of observables, each in the development normal form at the SAME
exponent `q ≥ 1`, is in the normal form at the sum of the majorants.  This is
the `ℝ≥0∞` triangle inequality of `l.bounds.mathcal.E.aL`'s Step 5, used for
the three summands of `e.apply.sensitivity.J.aL` and for the primal/adjoint
pair of `MajorantSlots.lFreeStep3Majorant`. -/
theorem lintegral_rpow_sum_le_of_moments {mu : Measure Omega} (t : Finset ι)
    {F : ι → Omega → ℝ≥0∞} {R : ι → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hFm : ∀ i ∈ t, AEMeasurable (F i) mu) (hR : ∀ i ∈ t, 0 ≤ R i)
    (hmom : ∀ i ∈ t, (∫⁻ omega, F i omega ^ q ∂mu) ≤ ENNReal.ofReal (R i) ^ q) :
    (∫⁻ omega, (∑ i ∈ t, F i omega) ^ q ∂mu) ≤ ENNReal.ofReal (∑ i ∈ t, R i) ^ q := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  -- the root form, proved by induction on the finset
  have key : ∀ u : Finset ι, u ⊆ t →
      (∫⁻ omega, (∑ i ∈ u, F i omega) ^ q ∂mu) ^ (1 / q) ≤ ∑ i ∈ u, ENNReal.ofReal (R i) := by
    intro u
    induction u using Finset.induction with
    | empty =>
        intro _
        rw [Finset.sum_empty]
        have hpt : ∀ omega : Omega, (∑ i ∈ (∅ : Finset ι), F i omega) ^ q = (0 : ℝ≥0∞) := by
          intro omega
          rw [Finset.sum_empty, ENNReal.zero_rpow_of_pos hq0]
        have hsimp : (∫⁻ omega, (∑ i ∈ (∅ : Finset ι), F i omega) ^ q ∂mu) = 0 := by
          calc (∫⁻ omega, (∑ i ∈ (∅ : Finset ι), F i omega) ^ q ∂mu)
              = ∫⁻ _omega : Omega, (0 : ℝ≥0∞) ∂mu := lintegral_congr hpt
            _ = 0 := lintegral_zero
        rw [hsimp, ENNReal.zero_rpow_of_pos (by positivity)]
    | insert i u hi ih =>
        intro hsub
        have hit : i ∈ t := hsub (Finset.mem_insert_self i u)
        have hut : u ⊆ t := fun x hx => hsub (Finset.mem_insert_of_mem hx)
        have hmeas : AEMeasurable (fun omega => ∑ j ∈ u, F j omega) mu := by
          have hsum := Finset.aemeasurable_sum u fun j hj => hFm j (hut hj)
          have hfun : (fun omega => ∑ j ∈ u, F j omega) = (∑ j ∈ u, F j) := by
            funext omega
            rw [Finset.sum_apply]
          rw [hfun]
          exact hsum
        have hmink : (∫⁻ omega, (F i omega + ∑ j ∈ u, F j omega) ^ q ∂mu) ^ (1 / q) ≤
            (∫⁻ omega, F i omega ^ q ∂mu) ^ (1 / q) +
              (∫⁻ omega, (∑ j ∈ u, F j omega) ^ q ∂mu) ^ (1 / q) :=
          ENNReal.lintegral_Lp_add_le (μ := mu) (f := F i)
            (g := fun omega => ∑ j ∈ u, F j omega) (hFm i hit) hmeas hq
        have hhead : (∫⁻ omega, F i omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal (R i) := by
          refine le_trans (ENNReal.rpow_le_rpow (hmom i hit) (by positivity)) (le_of_eq ?_)
          rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one]
        have hrewrite : (∫⁻ omega, (∑ j ∈ insert i u, F j omega) ^ q ∂mu) =
            ∫⁻ omega, (F i omega + ∑ j ∈ u, F j omega) ^ q ∂mu :=
          lintegral_congr fun omega => by rw [Finset.sum_insert hi]
        rw [hrewrite, Finset.sum_insert hi]
        exact le_trans hmink (add_le_add hhead (ih hut))
  have hroot := key t (le_refl t)
  have hR0 : (0 : ℝ) ≤ ∑ i ∈ t, R i := Finset.sum_nonneg hR
  have hsum : (∑ i ∈ t, ENNReal.ofReal (R i)) = ENNReal.ofReal (∑ i ∈ t, R i) :=
    (ENNReal.ofReal_sum_of_nonneg hR).symm
  rw [hsum] at hroot
  have hraise := ENNReal.rpow_le_rpow hroot hq0.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one] at hraise

end

end Algsuperdiff.Section4.Provider.BoundsEaL
