/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStability

/-!
# Excess quasi-monotonicity (`hmono`) on the cube-sandwich family

`l.iteration.lemma` never displays the inequality

```
E_k ≤ κ · E_{k+1}
```

but it uses it twice: once in Step 2, where the shifted excess sum is
reabsorbed across its `h` end terms (`e.sum.excess.bound`, whose graph edge
records "the reabsorption crosses the `h` end-terms of the shifted sum using
the per-scale quasi-monotonicity `E_k ≤ κ E_{k+1}`, which is a consequence of
the definition together with the window sandwich"), and once implicitly inside
the printed reabsorption factor `3^{(d+2)h}`, which is `κ^h`.  It is the
`hmono` hypothesis of the proved iteration engine
(`IterationLemma.combinedBound`, `IterationLemma.iterationSlopeBound`).

This module proves it, from geometry alone, on the family the lemma actually assumes.

## The mechanism

The competitor set is the *same* set of affine functions for both windows, so the domain comparison
is competitor-by-competitor: for `W' ⊆ W` and every affine `ℓ`,

```
‖u − ℓ‖_{L̲²(W')} ≤ (|W|/|W'|)^{1/2} ‖u − ℓ‖_{L̲²(W)}     (Support.normalizedL2On_le_of_subset)
```

and the left-hand infimum is below every competitor
(`Support.affineExcessRaw_le_affineDistOn`), which gives
`affineExcessRaw W' u ≤ (|W|/|W'|)^{1/2} affineExcessRaw W u`.  Restoring the `|W|^{−1/d}`
normalizer of `Support.affineExcess` turns the exponent `1/2` into `1/d + 1/2`:

```
E(u, W') ≤ (|W|/|W'|)^{1/d + 1/2} E(u, W) .
```

## The constant actually obtained

On the sandwich `x + □_{k−2} ⊆ U_k ⊆ y + □_k` the one-scale ratio is
`|U_{k+1}|/|U_k| ≤ 3^{(k+1)d}/3^{(k−2)d} = 3^{3d}`, so the derived constant is
*exactly* the one already proved for slope stability,

```
κ = volumeRatioConstTriadic d = (3^{3d})^{1/d + 1/2} = 3^{3 + 3d/2} ,
```

with `1 ≤ κ` available as `one_le_volumeRatioConstTriadic` — so the engine's `hκ` slot is
discharged by the same object.  Nothing here is assumed: `volumeRatio_le_of_cubeSandwich` proves
the ratio bound from the two inclusions.

The route above gives `3 + 3d/2` (the `3` is `3d · (1/d)`, the `3d/2` is `3d ·
(1/2)`; `1 + 3d/2` would need the ratio `3^d` for the first summand and
`3^{3d}` for the second, so it cannot come from one ratio).  Since `3 + 3d/2 ≤
d + 2` fails for **every** `d ≥ 1`, the printed `3^{(d+2)h}` is too small at
the derived `κ` in every dimension, not only for `d ≥ 3`.  This module does not
change any statement: `κ` is an explicit `def` here and the caveat is's to
adjust.

## References

* ABK26, `e.excess.def`; `e.sum.excess.bound`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open Homogenization (Vec axisCube openCubeSet TriadicCube cubeScaleFactor)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### `MemLp` transfer across the nesting

The iteration engine reads `u` on every window of the family, while a caller typically knows
`u ∈ L²` on the largest one.  Restriction is monotone in the set, so `MemLp` transfers downwards;
this is the whole content. -/

/-- **`MemLp` restricts to a subwindow.**  `Measure.restrict_mono` plus `MemLp.mono_measure`. -/
theorem memLp_restrict_of_subset {W W' : Set (Vec d)} {f : Vec d → ℝ} {p : ENNReal}
    (hsub : W' ⊆ W) (hf : MemLp f p (volume.restrict W)) :
    MemLp f p (volume.restrict W') :=
  hf.mono_measure (Measure.restrict_mono hsub le_rfl)

/-- A nested family is monotone: `U a ⊆ U b` whenever `a ≤ b`. -/
theorem subset_of_nested_le {U : ℤ → Set (Vec d)} (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    {a b : ℤ} (hab : a ≤ b) : U a ⊆ U b := by
  induction b, hab using Int.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (hnest n)

/-- **`MemLp` on the top window of a nested family gives `MemLp` on every lower window.** -/
theorem memLp_of_nested_le {U : ℤ → Set (Vec d)} {u : Vec d → ℝ} {p : ENNReal} {m : ℤ}
    (hnest : ∀ k : ℤ, U k ⊆ U (k + 1)) (hu : MemLp u p (volume.restrict (U m))) :
    ∀ k : ℤ, k ≤ m → MemLp u p (volume.restrict (U k)) :=
  fun _ hk => memLp_restrict_of_subset (subset_of_nested_le hnest hk) hu

/-! ### Domain comparison for the excess -/

/-- **Domain comparison for the unnormalized excess.**  For `W' ⊆ W` of positive volume, with every
affine deviation of `u` square-integrable on `W`,

`min_ℓ ‖u − ℓ‖_{L̲²(W')} ≤ (|W|/|W'|)^{1/2} · min_ℓ ‖u − ℓ‖_{L̲²(W)}`.

Proved competitor-by-competitor: the seminorm comparison holds for each affine `ℓ`, and the
left-hand infimum is below every competitor. -/
theorem affineExcessRaw_le_of_subset {W W' : Set (Vec d)} {u : Vec d → ℝ}
    (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hint : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W) :
    affineExcessRaw W' u
      ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * affineExcessRaw W u := by
  have hr : 0 < Real.sqrt ((volume W).toReal / (volume W').toReal) :=
    Real.sqrt_pos.2 (div_pos hW hW')
  rw [← div_le_iff₀' hr]
  refine le_csInf (affineDistSet_nonempty W u) ?_
  rintro y ⟨q, rfl⟩
  rw [div_le_iff₀ hr]
  have hcmp : affineDistOn W' u q.1 q.2
      ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * affineDistOn W u q.1 q.2 :=
    normalizedL2On_le_of_subset hsub hW hW' (hint q.1 q.2)
  calc affineExcessRaw W' u ≤ affineDistOn W' u q.1 q.2 :=
        affineExcessRaw_le_affineDistOn W' u q.1 q.2
    _ ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * affineDistOn W u q.1 q.2 := hcmp
    _ = affineDistOn W u q.1 q.2
          * Real.sqrt ((volume W).toReal / (volume W').toReal) := by ring

/-- The `rpow` bookkeeping of the normalizer restoration, over abstract positive reals: no numeric
tactic ever sees a `Real.rpow` atom. -/
private theorem rpow_ratio_identity {A B e : ℝ} (hA : 0 < A) (hB : 0 < B) :
    B ^ (-e) * Real.sqrt (A / B) = (A / B) ^ (e + 1 / 2) * A ^ (-e) := by
  have hAB : (0 : ℝ) < A / B := div_pos hA hB
  have hAe : A ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hA e)
  have hBe : B ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hB e)
  have hhalf : (A / B) ^ ((1 : ℝ) / 2) = Real.sqrt (A / B) := (Real.sqrt_eq_rpow (A / B)).symm
  have hsplit : (A / B) ^ (e + 1 / 2) = A ^ e / B ^ e * Real.sqrt (A / B) := by
    rw [Real.rpow_add hAB, Real.div_rpow hA.le hB.le e, hhalf]
  rw [hsplit, Real.rpow_neg hA.le, Real.rpow_neg hB.le]
  field_simp

/-- **Domain comparison for the excess `E(u,W) = |W|^{−1/d} min_ℓ ‖u − ℓ‖_{L̲²(W)}`.**
For `W' ⊆ W` of positive volume,

`E(u, W') ≤ (|W|/|W'|)^{1/d + 1/2} · E(u, W)`,

the exponent splitting as `1/d` (restoring the two `|·|^{−1/d}` normalizers) plus `1/2` (the
seminorm volume ratio). -/
theorem affineExcess_le_of_subset {W W' : Set (Vec d)} {u : Vec d → ℝ}
    (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hint : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W) :
    affineExcess W' u
      ≤ ((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) * affineExcess W u := by
  have hraw := affineExcessRaw_le_of_subset hsub hW hW' hint
  have hBe : (0 : ℝ) ≤ ((volume W').toReal) ^ (-(d : ℝ)⁻¹) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hstep := mul_le_mul_of_nonneg_left hraw hBe
  have hid := rpow_ratio_identity (e := (d : ℝ)⁻¹) hW hW'
  calc affineExcess W' u
      = ((volume W').toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W' u := rfl
    _ ≤ ((volume W').toReal) ^ (-(d : ℝ)⁻¹)
          * (Real.sqrt ((volume W).toReal / (volume W').toReal) * affineExcessRaw W u) := hstep
    _ = (((volume W').toReal) ^ (-(d : ℝ)⁻¹)
          * Real.sqrt ((volume W).toReal / (volume W').toReal)) * affineExcessRaw W u := by ring
    _ = (((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
          * ((volume W).toReal) ^ (-(d : ℝ)⁻¹)) * affineExcessRaw W u := by rw [hid]
    _ = ((volume W).toReal / (volume W').toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) * affineExcess W u := by
        rw [affineExcess]
        ring

/-! ### The `hmono` producer -/

/-- **Excess quasi-monotonicity on an abstract nested family**, in the exact shape
the proved iteration engine consumes as `hmono`
(`IterationLemma.combinedBound`, `IterationLemma.iterationSlopeBound`, at `E:=
fun k => affineExcess (U k) u`):

`∀ k, E k ≤ κ * E (k + 1)`.

`hratio` is the only quantitative input; the cube-sandwich instance below *proves* it. -/
theorem affineExcess_quasiMonotone_of_nested (U : ℤ → Set (Vec d)) (u : Vec d → ℝ) {κ : ℝ}
    (hnest : ∀ k : ℤ, U k ⊆ U (k + 1)) (hvol : ∀ k : ℤ, 0 < (volume (U k)).toReal)
    (hint : ∀ (k : ℤ) (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) (U k))
    (hratio : ∀ k : ℤ,
      ((volume (U (k + 1))).toReal / (volume (U k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2) ≤ κ) :
    ∀ k : ℤ, affineExcess (U k) u ≤ κ * affineExcess (U (k + 1)) u := by
  intro k
  have hcmp := affineExcess_le_of_subset (hnest k) (hvol (k + 1)) (hvol k) (hint (k + 1))
  exact hcmp.trans
    (mul_le_mul_of_nonneg_right (hratio k) (affineExcess_nonneg (U (k + 1)) u))

/-! ### The consumption class: the triadic cube sandwich -/

/-- **The `hint` slot, discharged from the sandwich.**  On a window contained in a triadic cube
every affine function is bounded, hence in `L²`; with `u ∈ L²(W)` the square of every affine
deviation is integrable. -/
theorem integrableOn_sub_affineEval_sq_of_cubeSandwich {W : Set (Vec d)} {u : Vec d → ℝ}
    {Q₂ : TriadicCube d} (hmeas : MeasurableSet W) (hout : W ⊆ openCubeSet Q₂)
    (hu : MemLp u 2 (volume.restrict W)) (c : ℝ) (g : Vec d) :
    IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W := by
  have hout' : W ⊆ axisCube (fun i => ((Q₂.index i : ℝ) - 1 / 2) * cubeScaleFactor Q₂)
      (cubeScaleFactor Q₂) := by
    rw [openCubeSet_eq_axisCube Q₂] at hout
    exact hout
  have haff : MemLp (affineEval c g) 2 (volume.restrict W) :=
    memLp_affineEval_of_sandwich (cubeScaleFactor_pos Q₂) hmeas hout' c g
  have hmem : MemLp (fun x => u x - affineEval c g x) 2 (volume.restrict W) := hu.sub haff
  exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem

/-- **The `hvol` slot, discharged from the sandwich.**  The inner cube forces positive volume; the
outer inclusion is needed only for finiteness. -/
theorem volume_toReal_pos_of_cubeSandwich {W : Set (Vec d)} {j : ℤ} {Q₁ Q₂ : TriadicCube d}
    (h1 : Q₁.scale = j - 2) (hin : openCubeSet Q₁ ⊆ W) (hout : W ⊆ openCubeSet Q₂) :
    0 < (volume W).toReal :=
  lt_of_lt_of_le (by positivity) (volume_toReal_ge_of_cubeSandwich h1 hin hout)

/-- For a nested family sandwiched as `x + □_{k−2} ⊆ U_k ⊆ y + □_k` at every scale, with `u`
square-integrable on each window,

```
E(u, U_k) ≤ volumeRatioConstTriadic d · E(u, U_{k+1})   for every k ∈ ℤ,
```

Nothing is assumed beyond the two inclusions, nestedness, measurability and `u ∈ L²`: the volume
ratio, the positivity of the volumes and the integrability of every affine deviation are all
proved.  In particular there is **no** dimension hypothesis. -/
theorem affineExcess_quasiMonotone_of_cubeSandwich (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
    {Q₁ Q₂ : ℤ → TriadicCube d}
    (hs₁ : ∀ k : ℤ, (Q₁ k).scale = k - 2) (hs₂ : ∀ k : ℤ, (Q₂ k).scale = k)
    (hin : ∀ k : ℤ, openCubeSet (Q₁ k) ⊆ U k) (hout : ∀ k : ℤ, U k ⊆ openCubeSet (Q₂ k))
    (hmeas : ∀ k : ℤ, MeasurableSet (U k)) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hu : ∀ k : ℤ, MemLp u 2 (volume.restrict (U k))) :
    ∀ k : ℤ, affineExcess (U k) u ≤ volumeRatioConstTriadic d * affineExcess (U (k + 1)) u :=
  affineExcess_quasiMonotone_of_nested U u hnest
    (fun k => volume_toReal_pos_of_cubeSandwich (hs₁ k) (hin k) (hout k))
    (fun k c g => integrableOn_sub_affineEval_sq_of_cubeSandwich (hmeas k) (hout k) (hu k) c g)
    (volumeRatio_le_of_cubeSandwich hs₁ hs₂ hin hout)

/-- **The same statement in the `3^{−j}` normalizer of `e.excess.def.cubes`.**

The conversion costs exactly the factor `9 = 3^2` on the constant:

```
E^{scaled}_k ≤ 9 · volumeRatioConstTriadic d · E^{scaled}_{k+1} .
```

`0 < d` enters here and only here: the normalizer bridge identifies `|□_j|^{−1/d}` with `3^{−j}`. -/
theorem affineExcessScaled_quasiMonotone_of_cubeSandwich (hd : 0 < d) (U : ℤ → Set (Vec d))
    (u : Vec d → ℝ) {Q₁ Q₂ : ℤ → TriadicCube d}
    (hs₁ : ∀ k : ℤ, (Q₁ k).scale = k - 2) (hs₂ : ∀ k : ℤ, (Q₂ k).scale = k)
    (hin : ∀ k : ℤ, openCubeSet (Q₁ k) ⊆ U k) (hout : ∀ k : ℤ, U k ⊆ openCubeSet (Q₂ k))
    (hmeas : ∀ k : ℤ, MeasurableSet (U k)) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hu : ∀ k : ℤ, MemLp u 2 (volume.restrict (U k))) :
    ∀ k : ℤ, affineExcessScaled k (U k) u
      ≤ 9 * volumeRatioConstTriadic d * affineExcessScaled (k + 1) (U (k + 1)) u := by
  have hκ : (1 : ℝ) ≤ volumeRatioConstTriadic d := one_le_volumeRatioConstTriadic d
  have hmono := affineExcess_quasiMonotone_of_cubeSandwich U u hs₁ hs₂ hin hout hmeas hnest hu
  intro k
  have hlow : affineExcessScaled k (U k) u ≤ affineExcess (U k) u :=
    affineExcessScaled_le_affineExcess_of_cubeSandwich hd.ne' (hs₁ k) (hs₂ k) (hin k) (hout k) u
  have hhigh : affineExcess (U (k + 1)) u ≤ 9 * affineExcessScaled (k + 1) (U (k + 1)) u :=
    affineExcess_le_affineExcessScaled_of_cubeSandwich hd.ne' (hs₁ (k + 1)) (hs₂ (k + 1))
      (hin (k + 1)) (hout (k + 1)) u
  calc affineExcessScaled k (U k) u ≤ affineExcess (U k) u := hlow
    _ ≤ volumeRatioConstTriadic d * affineExcess (U (k + 1)) u := hmono k
    _ ≤ volumeRatioConstTriadic d * (9 * affineExcessScaled (k + 1) (U (k + 1)) u) :=
        mul_le_mul_of_nonneg_left hhigh (by linarith only [hκ])
    _ = 9 * volumeRatioConstTriadic d * affineExcessScaled (k + 1) (U (k + 1)) u := by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
