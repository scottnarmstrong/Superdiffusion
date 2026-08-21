/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundarySchauder

/-!
# The boundary datum leg `K_h`

`OneStepBoundarySchauder.exists_gradientHolder_boundary_raw` produces the Hölder
bound of the boundary branch against the excess minimum of the competitor on the
**doubled** window `reflectedWindow x m (n-2)`.  The consumer
(`OneStepConditional.excessDecay_oneStep_of_harmonicApprox`) wants it against the
excess on `U_2 = (x + □_{n-2}) ∩ □_m` plus an additive datum leg `K_h`:

```text
  K ≤ Csch · (3^{-n})^{1/2} · E(v, U_2) + K_h .
```

This module supplies the passage, and it *is* the definition of `K_h` in the
Lean surface.

## The split

`U_2 ⊆ reflectedWindow x m (n-2)`, and the two pieces `U_2` and
`reflectedWindow \ U_2` partition the doubled window.  For any affine competitor
`ℓ = (c,g)`,

```text
  E_raw(V, reflectedWindow) ≤ ‖V − ℓ‖_{L̲²(U_2)} + ‖V − ℓ‖_{L̲²(reflectedWindow \ U_2)} ,
```

because `|reflectedWindow| ≥ |U_2|` and `|reflectedWindow| ≥ |reflectedWindow \ U_2|`
make each normalized piece dominate its share of the whole (`normalizedL2On_le_add_of_subset`).
Taking `ℓ` to be a **minimizer** on `U_2` — the manuscript's `ℓ(v, U_2)`, carried
as a quantified datum exactly as everywhere else in this tree, see
`AffineMinimizerExistence` — turns the first summand into `E_raw(V, U_2)` and
leaves

```text
  boundaryDatumLeg x m n V c g = ‖V − ℓ(v,U_2)‖_{L̲²(reflectedWindow \ U_2)}
```

as the **only** boundary contribution.  It is the far-side (reflected) leg: on
the interior branch `reflectedWindow = U_2` and it is identically `0`
(`boundaryDatumLeg_of_unmet`), which is the Lean reading of the manuscript's
indicator `1_{{(x+□_n) ∩ ∂□_m ≠ ∅}}`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec volumeAverage openCubeSet originCube)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Subadditivity of `√` and the two-piece split -/

private theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hprod : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hexp : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [hexp]
    linarith only [hprod]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- **The two-piece split of a volume average.**  For `W ⊆ R` of finite volume,
each normalized piece dominates its share of the whole, so the average over `R`
is at most the sum of the averages over `W` and `R \ W`. -/
theorem volumeAverage_sq_le_add_of_subset {W R : Set (Vec d)} {f : Vec d → ℝ}
    (hWmeas : MeasurableSet W) (hsub : W ⊆ R) (hRtop : volume R ≠ ⊤)
    (hWpos : 0 < (volume W).toReal)
    (hint : IntegrableOn (fun y => f y ^ 2) R volume) :
    volumeAverage R (fun y => f y ^ 2)
      ≤ volumeAverage W (fun y => f y ^ 2) + volumeAverage (R \ W) (fun y => f y ^ 2) := by
  set g : Vec d → ℝ := fun y => f y ^ 2 with hgdef
  have hg0 : ∀ y, 0 ≤ g y := fun y => sq_nonneg (f y)
  have hWR : (volume W).toReal ≤ (volume R).toReal :=
    ENNReal.toReal_mono hRtop (measure_mono hsub)
  have hDR : (volume (R \ W)).toReal ≤ (volume R).toReal :=
    ENNReal.toReal_mono hRtop (measure_mono Set.diff_subset)
  have hsplit : (∫ y in W, g y) + (∫ y in R \ W, g y) = ∫ y in R, g y := by
    have h := MeasureTheory.integral_inter_add_diff (μ := (volume : Measure (Vec d)))
      (s := R) (t := W) (f := g) hWmeas hint
    rwa [Set.inter_eq_self_of_subset_right hsub] at h
  have hWint : (0 : ℝ) ≤ ∫ y in W, g y := integral_nonneg hg0
  have hDint : (0 : ℝ) ≤ ∫ y in R \ W, g y := integral_nonneg hg0
  have h1 : ((volume R).toReal)⁻¹ * ∫ y in W, g y
      ≤ ((volume W).toReal)⁻¹ * ∫ y in W, g y :=
    mul_le_mul_of_nonneg_right (inv_anti₀ hWpos hWR) hWint
  have h2 : ((volume R).toReal)⁻¹ * ∫ y in R \ W, g y
      ≤ ((volume (R \ W)).toReal)⁻¹ * ∫ y in R \ W, g y := by
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg :
        (0 : ℝ) ≤ (volume (R \ W)).toReal) with h0 | h0
    · have hne : volume (R \ W) ≠ ⊤ :=
        ne_top_of_le_ne_top hRtop (measure_mono Set.diff_subset)
      have hz : volume (R \ W) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (volume (R \ W))).1 h0.symm with h | h
        · exact h
        · exact absurd h hne
      have hzero : (∫ y in R \ W, g y) = 0 :=
        MeasureTheory.setIntegral_measure_zero g hz
      rw [hzero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (inv_anti₀ h0 hDR) hDint
  unfold volumeAverage
  rw [← hsplit, mul_add]
  linarith only [h1, h2]

/-- **The two-piece split of the normalized seminorm.** -/
theorem normalizedL2On_le_add_of_subset {W R : Set (Vec d)} {f : Vec d → ℝ}
    (hWmeas : MeasurableSet W) (hsub : W ⊆ R) (hRtop : volume R ≠ ⊤)
    (hWpos : 0 < (volume W).toReal)
    (hint : IntegrableOn (fun y => f y ^ 2) R volume) :
    normalizedL2On R f ≤ normalizedL2On W f + normalizedL2On (R \ W) f := by
  have h := volumeAverage_sq_le_add_of_subset hWmeas hsub hRtop hWpos hint
  unfold normalizedL2On
  calc Real.sqrt (volumeAverage R fun y => f y ^ 2)
      ≤ Real.sqrt ((volumeAverage W fun y => f y ^ 2)
          + (volumeAverage (R \ W) fun y => f y ^ 2)) := Real.sqrt_le_sqrt h
    _ ≤ Real.sqrt (volumeAverage W fun y => f y ^ 2)
          + Real.sqrt (volumeAverage (R \ W) fun y => f y ^ 2) :=
        sqrt_add_le_sqrt_add_sqrt (volumeAverage_sq_nonneg W f)
          (volumeAverage_sq_nonneg (R \ W) f)

/-! ## 2. The datum leg -/

/-- **The boundary datum leg.**  The far-side (reflected) part of the competitor's
distance to the affine competitor `ℓ = (c,g)`.  This is the Lean surface's `K_h`,
up to the explicit prefactor of `exists_gradientHolder_boundary_split`. -/
def boundaryDatumLeg (x : Vec d) (m n : ℤ) (V : Vec d → ℝ) (c : ℝ) (g : Vec d) : ℝ :=
  normalizedL2On (reflectedWindow x m (n - 2) \ truncatedWindow x m (n - 2))
    fun y => V y - affineEval c g y

theorem boundaryDatumLeg_nonneg (x : Vec d) (m n : ℤ) (V : Vec d → ℝ) (c : ℝ) (g : Vec d) :
    0 ≤ boundaryDatumLeg x m n V c g :=
  normalizedL2On_nonneg _ _

/-! ## 3. The leg vanishes when no face is met -/

theorem normalizedL2On_empty (f : Vec d → ℝ) : normalizedL2On (∅ : Set (Vec d)) f = 0 := by
  unfold normalizedL2On volumeAverage
  simp

/-- If no face of `∂□_m` is met, the partial reflection is the window itself. -/
theorem reflectedWindow_eq_truncatedWindow_of_unmet {x : Vec d} {m k : ℤ}
    (hunmet : ∀ i, ¬ MeetsUpperFace x m k i ∧ ¬ MeetsLowerFace x m k i) :
    reflectedWindow x m k = truncatedWindow x m k := by
  rw [truncatedWindow_eq_coordBox, reflectedWindow]
  congr 1
  · funext i
    exact reflectedLo_of_not_meetsLowerFace (hunmet i).2
  · funext i
    exact reflectedHi_of_not_meetsUpperFace (hunmet i).1

/-- **The datum leg is exactly the boundary contribution.**  When no face of
`∂□_m` is met — the interior branch, i.e. the manuscript's indicator
`1_{{(x+□_n) ∩ ∂□_m ≠ ∅}}` evaluating to `0` — the leg vanishes identically. -/
theorem boundaryDatumLeg_of_unmet {x : Vec d} {m n : ℤ}
    (hunmet : ∀ i, ¬ MeetsUpperFace x m (n - 2) i ∧ ¬ MeetsLowerFace x m (n - 2) i)
    (V : Vec d → ℝ) (c : ℝ) (g : Vec d) : boundaryDatumLeg x m n V c g = 0 := by
  rw [boundaryDatumLeg, reflectedWindow_eq_truncatedWindow_of_unmet hunmet, Set.diff_self]
  exact normalizedL2On_empty _

/-! ## 4. The excess bridge -/

/-- **The boundary excess bridge.**  The excess minimum on the doubled window is
at most the distance to any affine competitor on `U_2` plus that competitor's
far-side leg. -/
theorem affineExcessRaw_reflectedWindow_le {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    {V : Vec d → ℝ}
    (hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (V y - affineEval c g y) ^ 2)
        (reflectedWindow x m (n - 2)) volume)
    (c : ℝ) (g : Vec d) :
    affineExcessRaw (reflectedWindow x m (n - 2)) V
      ≤ affineDistOn (truncatedWindow x m (n - 2)) V c g + boundaryDatumLeg x m n V c g := by
  refine le_trans (affineExcessRaw_le_affineDistOn _ _ c g) ?_
  rw [affineDistOn, affineDistOn, boundaryDatumLeg]
  exact normalizedL2On_le_add_of_subset
    (measurableSet_truncatedWindow x m (n - 2))
    (truncatedWindow_subset_reflectedWindow x m (n - 2))
    (volume_reflectedWindow_ne_top x m (n - 2))
    (volume_toReal_truncatedWindow_pos x hx (by omega))
    (hintsq c g)

/-! ## 5. The producer in the consumer's shape -/

/-- **The Schauder gradient-Hölder estimate, boundary branch — the producer in the
consumer's shape.**

For `V` classically harmonic on the doubled window and `(c,g)` an affine
minimizer for `V` on `U_2 = (x + □_{n-2}) ∩ □_m` (the manuscript's `ℓ(v,U_2)`),
the gradient field realizes the four slots
`hint / hgrad / hhol / hschauder` of
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` with

```text
  Csch = boundarySchauderConst d ,
  K_h  = boundarySchauderConst d · (3^{-n})^{1/2} · (3^{-(n-2)} · boundaryDatumLeg …) ,
```

`K_h` being `0` on the interior branch (`boundaryDatumLeg_of_unmet`). -/
theorem exists_gradientHolder_boundary_split [NeZero d] (hd : d ≠ 0) {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    {V : Vec d → ℝ}
    (hharm : HarmonicOnNhd (V ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (V y - affineEval c g y) ^ 2)
        (reflectedWindow x m (n - 2)) volume)
    {c : ℝ} {g : Vec d} (hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) V c g) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField V p i) (truncatedWindow x m (n - 3)) volume) ∧
      HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
      HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
      K ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m (n - 2)) V
          + boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * ((3 : ℝ) ^ (-(n - 2)) * boundaryDatumLeg x m n V c g) := by
  obtain ⟨K, hK, hint, hgrad, hhol, hraw⟩ :=
    exists_gradientHolder_boundary_raw hx hmn hharm hintsq
  refine ⟨K, hK, hint, hgrad, hhol, le_trans hraw ?_⟩
  have hkappa : (0 : ℝ) ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) :=
    mul_nonneg (boundarySchauderConst_nonneg d) (Real.rpow_nonneg (by positivity) _)
  have hmin' : affineDistOn (truncatedWindow x m (n - 2)) V c g
      = affineExcessRaw (truncatedWindow x m (n - 2)) V := hmin
  have hbridge : affineExcessRaw (reflectedWindow x m (n - 2)) V
      ≤ affineExcessRaw (truncatedWindow x m (n - 2)) V + boundaryDatumLeg x m n V c g := by
    have h := affineExcessRaw_reflectedWindow_le hx hmn hintsq c g
    rwa [hmin'] at h
  have hscale : (0 : ℝ) < (3 : ℝ) ^ (-(n - 2)) := zpow_pos (by norm_num) _
  have hnorm : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V
      ≤ affineExcess (truncatedWindow x m (n - 2)) V := by
    rw [affineExcess]
    exact mul_le_mul_of_nonneg_right
      (rpow_volume_truncatedWindow_bounds hd x hx (by omega)).1
      (affineExcessRaw_nonneg _ _)
  have hstep : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (reflectedWindow x m (n - 2)) V
      ≤ affineExcess (truncatedWindow x m (n - 2)) V
        + (3 : ℝ) ^ (-(n - 2)) * boundaryDatumLeg x m n V c g := by
    have h1 := mul_le_mul_of_nonneg_left hbridge hscale.le
    rw [mul_add] at h1
    linarith only [h1, hnorm]
  calc boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (reflectedWindow x m (n - 2)) V)
      ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * (affineExcess (truncatedWindow x m (n - 2)) V
            + (3 : ℝ) ^ (-(n - 2)) * boundaryDatumLeg x m n V c g) :=
        mul_le_mul_of_nonneg_left hstep hkappa
    _ = boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * affineExcess (truncatedWindow x m (n - 2)) V
        + boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * ((3 : ℝ) ^ (-(n - 2)) * boundaryDatumLeg x m n V c g) := by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
