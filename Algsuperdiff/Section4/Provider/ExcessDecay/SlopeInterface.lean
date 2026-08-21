/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.QuasiMonotone

/-!
# The one-sided slope-stability interface and the slope telescope

`e.grad.stability` is printed two-sided,

```
|∇ℓ_k − ∇ℓ_{k−1}| ≤ C (E_k + E_{k−1}) ,
```

and that is the form the proved producer proves
(`SlopeStability.slopeStability_of_cubeSandwich_explicit`).  The revision paper
states the same estimate one-sidedly, `|P_{r+1,j} − P_{r,j}| ≤{r+1,j}`, with
the justification spelled out: "the minimizer on `□_{r+1}` is admissible after
restriction to `□_r`, so `E_r ≤{r+1}`; this absorbs the symmetric-looking
contribution into the single term displayed".

```
|∇ℓ_a| ≤ |∇ℓ_b| + C ∑_{k=a+1}^{b} E_k
```

is one line and needs no index-shift bookkeeping.

## What the one-sided form buys, precisely

The abstract conversion is `abs_sub_le_oneSided_of_quasiMonotone`: `E_{k−1} ≤ κ E_k` turns
`C (E_k + E_{k−1})` into `C (1 + κ) E_k`, so the constant is

```
oneSidedSlopeConst d θ κ = slopeStabilityConst d θ κ · (1 + κ) ,
```

and on the §4.3 consumption class `oneSidedSlopeConstTriadic d` at `θ = 3^{−2}`,
`κ = volumeRatioConstTriadic d` --- a closed-form function of `d` alone.

The telescope then costs `C`, not `2C`, and runs over the half-open run `(a,
b]`: `slopeTelescopeOneSided`.  Compare the proved two-sided
`IterationCore.slopeTelescope`, which pays the factor `2` (each `E_k` occurs in
two telescoped pairs) and sums over the *closed* `[b − l, b]` with a `ℕ`-valued
length.

## References

* ABK26, `e.grad.stability`; the telescoping step.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open Homogenization (Vec openCubeSet TriadicCube)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### The one-sided constant -/

/-- The **one-sided slope-stability constant** `C(1 + κ)`: the two-sided constant of
`e.grad.stability` times the quasi-monotonicity loss incurred by moving `E_{k−1}` up to `E_k`.
Explicitly a function of `(d, θ, κ)`; no existential. -/
def oneSidedSlopeConst (d : ℕ) (θ κ : ℝ) : ℝ := slopeStabilityConst d θ κ * (1 + κ)

theorem oneSidedSlopeConst_nonneg {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    0 ≤ oneSidedSlopeConst d θ κ :=
  mul_nonneg (slopeStabilityConst_nonneg hθ hκ) (by linarith only [hκ])

/-- The one-sided constant on the §4.3 consumption class: aspect ratio `θ = 1/9` (the printed
`3^{−2}`) and `κ = volumeRatioConstTriadic d`, hence a closed-form function of `d` alone. -/
def oneSidedSlopeConstTriadic (d : ℕ) : ℝ :=
  oneSidedSlopeConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d)

theorem oneSidedSlopeConstTriadic_nonneg (d : ℕ) : 0 ≤ oneSidedSlopeConstTriadic d :=
  oneSidedSlopeConst_nonneg (by norm_num)
    (le_trans zero_le_one (one_le_volumeRatioConstTriadic d))

/-! ### Two-sided to one-sided -/

/-- **The conversion, abstractly.**  Quasi-monotonicity moves the smaller-scale
excess up, so a two-sided slope-difference bound becomes a one-sided one with
*every* right-hand quantity at the larger window.  No nonnegativity of `E` is
needed, and `κ` is not required to be `≥ 1`. -/
theorem abs_sub_le_oneSided_of_quasiMonotone {E p : ℤ → ℝ} {C κ : ℝ} (hC : 0 ≤ C)
    (hmono : ∀ k : ℤ, E k ≤ κ * E (k + 1))
    (htwo : ∀ k : ℤ, |p k - p (k - 1)| ≤ C * (E k + E (k - 1))) :
    ∀ k : ℤ, |p k - p (k - 1)| ≤ C * (1 + κ) * E k := by
  intro k
  have hm : E (k - 1) ≤ κ * E k := by
    have h := hmono (k - 1)
    rw [sub_add_cancel] at h
    exact h
  have hmul : C * E (k - 1) ≤ C * (κ * E k) := mul_le_mul_of_nonneg_left hm hC
  exact (htwo k).trans (by linarith only [hmul])

/-- **One-sided gradient stability on the §4.3 consumption class.**

On the paper's window family `x + □_{k−2} ⊆ U_k ⊆ y + □_k`, with `u` square-integrable on each
window and `(cc k, gg k)` a chosen affine minimizer on `U k`,

```
| |∇ℓ_k| − |∇ℓ_{k−1}| | ≤ oneSidedSlopeConstTriadic d · E(u, U_k) ,
```

with the right-hand side read entirely at the *larger* window `U_k`. -/
theorem slopeStability_oneSided_of_cubeSandwich (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
    (cc : ℤ → ℝ) (gg : ℤ → Vec d) {Q₁ Q₂ : ℤ → TriadicCube d}
    (hd : 0 < d) (hs₁ : ∀ k : ℤ, (Q₁ k).scale = k - 2) (hs₂ : ∀ k : ℤ, (Q₂ k).scale = k)
    (hin : ∀ k : ℤ, openCubeSet (Q₁ k) ⊆ U k) (hout : ∀ k : ℤ, U k ⊆ openCubeSet (Q₂ k))
    (hmeas : ∀ k : ℤ, MeasurableSet (U k)) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hu : ∀ k : ℤ, MemLp u 2 (volume.restrict (U k)))
    (hmin : ∀ k : ℤ, IsAffineMinimizer (U k) u (cc k) (gg k)) :
    ∀ k : ℤ, |slopeMagnitude (gg k) - slopeMagnitude (gg (k - 1))|
      ≤ oneSidedSlopeConstTriadic d * affineExcess (U k) u := by
  have htwo := slopeStability_of_cubeSandwich_explicit U u cc gg hd hs₁ hs₂ hin hout hmeas
    hnest hu hmin
  have hmono := affineExcess_quasiMonotone_of_cubeSandwich U u hs₁ hs₂ hin hout hmeas hnest hu
  have hC : (0 : ℝ) ≤ slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d) :=
    slopeStabilityConst_nonneg (by norm_num)
      (le_trans zero_le_one (one_le_volumeRatioConstTriadic d))
  exact abs_sub_le_oneSided_of_quasiMonotone hC hmono htwo

/-- The same bound in the index-shifted form the sub-window absorption reads: the increment from
scale `k` to scale `k+1` is controlled by the excess at `k+1`. -/
theorem slopeStability_oneSided_succ_of_cubeSandwich (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
    (cc : ℤ → ℝ) (gg : ℤ → Vec d) {Q₁ Q₂ : ℤ → TriadicCube d}
    (hd : 0 < d) (hs₁ : ∀ k : ℤ, (Q₁ k).scale = k - 2) (hs₂ : ∀ k : ℤ, (Q₂ k).scale = k)
    (hin : ∀ k : ℤ, openCubeSet (Q₁ k) ⊆ U k) (hout : ∀ k : ℤ, U k ⊆ openCubeSet (Q₂ k))
    (hmeas : ∀ k : ℤ, MeasurableSet (U k)) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hu : ∀ k : ℤ, MemLp u 2 (volume.restrict (U k)))
    (hmin : ∀ k : ℤ, IsAffineMinimizer (U k) u (cc k) (gg k)) :
    ∀ k : ℤ, |slopeMagnitude (gg (k + 1)) - slopeMagnitude (gg k)|
      ≤ oneSidedSlopeConstTriadic d * affineExcess (U (k + 1)) u := by
  intro k
  have h := slopeStability_oneSided_of_cubeSandwich U u cc gg hd hs₁ hs₂ hin hout hmeas hnest
    hu hmin (k + 1)
  rw [add_sub_cancel_right] at h
  exact h

/-! ### The slope telescope -/

/-- **The one-sided slope telescope.**  With every right-hand side at the larger
scale the telescope is one induction: for `a ≤ b`,

```
|p_b − p_a| ≤ C ∑_{k=a+1}^{b} E_k ,
```

the sum running over the half-open `(a, b]` and the constant being `C`, not `2C`, because each
`E_k` now occurs in exactly one telescoped pair.  Neither `0 ≤ C` nor `0 ≤ E` is needed. -/
theorem slopeTelescopeOneSided {E p : ℤ → ℝ} {C : ℝ}
    (hone : ∀ k : ℤ, |p k - p (k - 1)| ≤ C * E k) {a b : ℤ} (hab : a ≤ b) :
    |p b - p a| ≤ C * ∑ k ∈ Finset.Icc (a + 1) b, E k := by
  induction b, hab using Int.le_induction with
  | base =>
    have hemp : Finset.Icc (a + 1) a = (∅ : Finset ℤ) :=
      Finset.Icc_eq_empty_of_lt (by omega)
    exact le_of_eq (by rw [hemp, Finset.sum_empty, mul_zero, sub_self, abs_zero])
  | succ n hn ih =>
    have hins : Finset.Icc (a + 1) (n + 1) = insert (n + 1) (Finset.Icc (a + 1) n) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot : (n + 1) ∉ Finset.Icc (a + 1) n := by
      simp only [Finset.mem_Icc]
      omega
    have hstep : |p (n + 1) - p n| ≤ C * E (n + 1) := by
      have h := hone (n + 1)
      rw [add_sub_cancel_right] at h
      exact h
    have htri : |p (n + 1) - p a| ≤ |p (n + 1) - p n| + |p n - p a| := by
      have hsplit : p (n + 1) - p a = (p (n + 1) - p n) + (p n - p a) := by ring
      rw [hsplit]
      exact abs_add_le _ _
    rw [hins, Finset.sum_insert hnot, mul_add]
    linarith only [htri, hstep, ih]

/-- The telescope in the form the revision uses: the slope at the inner scale is the slope at the
outer scale plus the excess sum over the run. -/
theorem le_add_sum_of_oneSided {E p : ℤ → ℝ} {C : ℝ}
    (hone : ∀ k : ℤ, |p k - p (k - 1)| ≤ C * E k) {a b : ℤ} (hab : a ≤ b) :
    p a ≤ p b + C * ∑ k ∈ Finset.Icc (a + 1) b, E k := by
  have h := slopeTelescopeOneSided hone hab
  have h1 : -(C * ∑ k ∈ Finset.Icc (a + 1) b, E k) ≤ p b - p a := (abs_le.1 h).1
  linarith only [h1]

/-- **The slope telescope on the §4.3 consumption class.**  The one-line sum: for `a ≤ b`,

```
| |∇ℓ_b| − |∇ℓ_a| | ≤ oneSidedSlopeConstTriadic d · ∑_{k=a+1}^{b} E(u, U_k) .
```
-/
theorem slopeMagnitude_telescope_of_cubeSandwich (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
    (cc : ℤ → ℝ) (gg : ℤ → Vec d) {Q₁ Q₂ : ℤ → TriadicCube d}
    (hd : 0 < d) (hs₁ : ∀ k : ℤ, (Q₁ k).scale = k - 2) (hs₂ : ∀ k : ℤ, (Q₂ k).scale = k)
    (hin : ∀ k : ℤ, openCubeSet (Q₁ k) ⊆ U k) (hout : ∀ k : ℤ, U k ⊆ openCubeSet (Q₂ k))
    (hmeas : ∀ k : ℤ, MeasurableSet (U k)) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hu : ∀ k : ℤ, MemLp u 2 (volume.restrict (U k)))
    (hmin : ∀ k : ℤ, IsAffineMinimizer (U k) u (cc k) (gg k)) :
    ∀ a b : ℤ, a ≤ b →
      |slopeMagnitude (gg b) - slopeMagnitude (gg a)|
        ≤ oneSidedSlopeConstTriadic d * ∑ k ∈ Finset.Icc (a + 1) b, affineExcess (U k) u := by
  have hone := slopeStability_oneSided_of_cubeSandwich U u cc gg hd hs₁ hs₂ hin hout hmeas
    hnest hu hmin
  exact fun a b hab => slopeTelescopeOneSided (p := fun k => slopeMagnitude (gg k))
    (E := fun k => affineExcess (U k) u) hone hab

/-- **The consumed form of the telescope**: the inner slope is dominated by the outer slope plus
the excess sum, which is what the sub-window reabsorption of the iteration lemma reads. -/
theorem slopeMagnitude_le_of_cubeSandwich (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
    (cc : ℤ → ℝ) (gg : ℤ → Vec d) {Q₁ Q₂ : ℤ → TriadicCube d}
    (hd : 0 < d) (hs₁ : ∀ k : ℤ, (Q₁ k).scale = k - 2) (hs₂ : ∀ k : ℤ, (Q₂ k).scale = k)
    (hin : ∀ k : ℤ, openCubeSet (Q₁ k) ⊆ U k) (hout : ∀ k : ℤ, U k ⊆ openCubeSet (Q₂ k))
    (hmeas : ∀ k : ℤ, MeasurableSet (U k)) (hnest : ∀ k : ℤ, U k ⊆ U (k + 1))
    (hu : ∀ k : ℤ, MemLp u 2 (volume.restrict (U k)))
    (hmin : ∀ k : ℤ, IsAffineMinimizer (U k) u (cc k) (gg k)) :
    ∀ a b : ℤ, a ≤ b →
      slopeMagnitude (gg a) ≤ slopeMagnitude (gg b)
        + oneSidedSlopeConstTriadic d * ∑ k ∈ Finset.Icc (a + 1) b, affineExcess (U k) u := by
  have hone := slopeStability_oneSided_of_cubeSandwich U u cc gg hd hs₁ hs₂ hin hout hmeas
    hnest hu hmin
  exact fun a b hab => le_add_sum_of_oneSided (p := fun k => slopeMagnitude (gg k))
    (E := fun k => affineExcess (U k) u) hone hab

end

end Algsuperdiff.Section4.Provider.ExcessDecay
