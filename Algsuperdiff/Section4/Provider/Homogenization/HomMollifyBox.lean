/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomLiftEndpoint
import Algsuperdiff.Section4.Provider.Homogenization.HomLiftNegativeNorm
import Homogenization.Geometry.CubeMetric
import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.StoppingRadius

/-!
# Theorem B, §4.5, Step 3c: the translated-box average carrier

## What this module supplies

The mollifier calculus is the remaining ingredient of the lifting: the two
scale-by-scale estimates

```text
  (L)  |W_n(x) - W_n(y)| ≤ A · 3^{-ns} · |x - y|
  (I)  |W_n(x) - W_{n-1}(x)| ≤ A · 3^{n(1-s)}
```

for a regularization family `W_n` of `w`.  Both descend from one bound on
the *gradient* of the regularization, `|∇W_n| ≤ A 3^{-ns}`; and since
`∇(w ⋆ φ) = (∇w) ⋆ φ`, that bound is a statement about the pairing of `∇w`
against the mollifier.  The only information about `∇w` the manuscript
supplies is its negative-order gauge — i.e. its **cube averages**.  This
module builds the carrier those averages live on, in the form the mollifier
calculus needs: the average over the box of side `3^n` centred at an
*arbitrary* point, not only at a triadic grid point.

## The sup-norm coincidence

`Vec d = Fin d → ℝ` carries the supremum norm, so `Metric.closedBall x r` is
*exactly* the axis-parallel box `x + [-r,r]^d`.  The scale-`n` box centred at
`x` is therefore `Metric.closedBall x (3^n/2)`, and `CoarseGraining`'s
`closedBallAverage` is already the sliding box average.  Everything below is
phrased through that identification, which buys the volume formula, the
convexity needed for the mean value inequality, and `CoarseGraining`'s Lebesgue
differentiation for translated boxes.

## The grid/translate distinction (this file's central structural finding)

The negative Besov seminorm definition sums over `z ∈ 3^n ℤ^d ∩ □_m`: the
depth-`j` quantity of the `negBesovInftyNorm` is a maximum over the **triadic
grid** `descendantsAtDepth Q j`.  A mollifier centred at a general point `x`
sees the box `x + □_n`, which is *not* a grid cube.  The two gauges are related
in exactly one elementary direction,

```text
  grid gauge  ≤  √d · translate gauge · 3^{-s·scale},
```

because every grid cube *is* a translate (`cubeAverage_eq_boxAverage`).  The
converse — reconstructing a translate average from the grid averages at all
scales — is true, but is a genuine martingale/telescoping argument over the
triadic filtration; see the "reconstruction residue" section of
`HomMollifyPairing`.  Accordingly the mollifier calculus of this file runs on
the *translate* gauge `UniformBoxGaugeBound`, and
`negBesovInftyNorm_le_of_uniformBoxGauge` records exactly how much stronger
that hypothesis is.

## Main definitions and results

* `boxRadius n` — the half-side `3^n/2`; `boxSet n x` — the scale-`n` box
  centred at `x`, i.e. `Metric.closedBall x (boxRadius n)`.
* `volume_boxSet`, `measurableSet_boxSet`, `convex_boxSet`, `isCompact_boxSet`.
* `boxAverage`, `boxAverageVec` — the scalar and vector sliding averages,
  defined through `CoarseGraining`'s `closedBallAverage`.
* `cubeAverage_eq_boxAverage`, `cubeAverageVec_eq_boxAverageVec` — every `CoarseGraining`
  triadic cube average is a box average at the cube's centre.
* `UniformBoxGaugeBound m s A F` — the translate-uniform negative gauge of
  order `-s`: `‖(F)_{x+□_n}‖ ≤ A 3^{-ns}` for every `n ≤ m` and every `x`.
* `negBesovInftyNorm_le_of_uniformBoxGauge` — the comparison with the grid
  gauge, at the explicit dimensional factor `√d`.

## References

* ABK26, the negative Besov seminorm definition.
* ABK26, Theorem B Step 3.
-/

open MeasureTheory Homogenization Homogenization.CubeCalderonZygmund

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The translated box -/

/-- The half-side of the scale-`n` box. -/
def boxRadius (n : ℤ) : ℝ := (3 : ℝ) ^ (n : ℝ) / 2

theorem boxRadius_def (n : ℤ) : boxRadius n = (3 : ℝ) ^ (n : ℝ) / 2 := rfl

theorem boxRadius_pos (n : ℤ) : 0 < boxRadius n := by
  rw [boxRadius_def]
  exact half_pos (three_rpow_pos _)

theorem two_mul_boxRadius (n : ℤ) : 2 * boxRadius n = (3 : ℝ) ^ (n : ℝ) := by
  rw [boxRadius_def]; ring

/-- **The scale-`n` box centred at `x`.**  In the supremum norm of `Vec d`
the closed metric ball is the axis-parallel box of side `2r`, so this is the
manuscript's `x + □_n`. -/
def boxSet (n : ℤ) (x : Vec d) : Set (Vec d) := Metric.closedBall x (boxRadius n)

theorem boxSet_def (n : ℤ) (x : Vec d) : boxSet n x = Metric.closedBall x (boxRadius n) := rfl

theorem mem_boxSet_iff {n : ℤ} {x y : Vec d} : y ∈ boxSet n x ↔ ‖y - x‖ ≤ boxRadius n := by
  rw [boxSet_def, Metric.mem_closedBall, dist_eq_norm]

theorem self_mem_boxSet (n : ℤ) (x : Vec d) : x ∈ boxSet n x :=
  Metric.mem_closedBall_self (boxRadius_pos n).le

theorem measurableSet_boxSet (n : ℤ) (x : Vec d) : MeasurableSet (boxSet (d := d) n x) :=
  measurableSet_closedBall

theorem convex_boxSet (n : ℤ) (x : Vec d) : Convex ℝ (boxSet (d := d) n x) :=
  convex_closedBall x (boxRadius n)

theorem isCompact_boxSet (n : ℤ) (x : Vec d) : IsCompact (boxSet (d := d) n x) :=
  isCompact_closedBall x (boxRadius n)

/-- **The volume of the box** is the `d`-th power of its side length. -/
theorem volume_boxSet (n : ℤ) (x : Vec d) :
    volume (boxSet n x) = ENNReal.ofReal (((3 : ℝ) ^ (n : ℝ)) ^ d) := by
  rw [boxSet_def, Real.volume_pi_closedBall x (boxRadius_pos n).le, two_mul_boxRadius,
    Fintype.card_fin]

theorem boxVolume_pos (n : ℤ) : (0 : ℝ) < ((3 : ℝ) ^ (n : ℝ)) ^ d :=
  pow_pos (three_rpow_pos _) d

theorem toReal_volume_boxSet (n : ℤ) (x : Vec d) :
    (volume (boxSet n x)).toReal = ((3 : ℝ) ^ (n : ℝ)) ^ d := by
  rw [volume_boxSet, ENNReal.toReal_ofReal (boxVolume_pos n).le]

theorem volume_boxSet_lt_top (n : ℤ) (x : Vec d) : volume (boxSet n x) < ⊤ := by
  rw [volume_boxSet]; exact ENNReal.ofReal_lt_top

/-! ## 2. The box averages -/

/-- The **average of a scalar field over the scale-`n` box centred at `x`**,
`CoarseGraining`'s sliding closed-ball average at the half-side `3^n/2`. -/
def boxAverage (n : ℤ) (x : Vec d) (f : Vec d → ℝ) : ℝ :=
  closedBallAverage x (boxRadius n) f

/-- The coordinatewise average of a vector field over the same box. -/
def boxAverageVec (n : ℤ) (x : Vec d) (F : Vec d → Vec d) : Vec d :=
  fun i => boxAverage n x fun y => F y i

theorem boxAverage_def (n : ℤ) (x : Vec d) (f : Vec d → ℝ) :
    boxAverage n x f = closedBallAverage x (boxRadius n) f := rfl

theorem boxAverageVec_apply (n : ℤ) (x : Vec d) (F : Vec d → Vec d) (i : Fin d) :
    boxAverageVec n x F i = boxAverage n x fun y => F y i := rfl

/-- The unpacked form: the box integral divided by the box volume. -/
theorem boxAverage_eq_inv_mul_integral (n : ℤ) (x : Vec d) (f : Vec d → ℝ) :
    boxAverage n x f = (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹ * ∫ y in boxSet n x, f y := by
  rw [boxAverage_def, closedBallAverage, boxSet_def, two_mul_boxRadius]

theorem boxAverage_eq_setAverage (n : ℤ) (x : Vec d) (f : Vec d → ℝ) :
    boxAverage n x f = ⨍ y in boxSet n x, f y :=
  closedBallAverage_eq_setAverage x (boxRadius_pos n).le f

/-- A uniform pointwise bound on the box passes to the average. -/
theorem abs_boxAverage_le {n : ℤ} {x : Vec d} {f : Vec d → ℝ} {C : ℝ}
    (hf : ∀ y ∈ boxSet n x, |f y| ≤ C) : |boxAverage n x f| ≤ C := by
  have hvol : (0 : ℝ) < ((3 : ℝ) ^ (n : ℝ)) ^ d := boxVolume_pos n
  have hbound : ‖∫ y in boxSet n x, f y‖ ≤ C * (volume (boxSet n x)).toReal := by
    refine norm_setIntegral_le_of_norm_le_const (volume_boxSet_lt_top n x) ?_
    intro y hy
    rw [Real.norm_eq_abs]
    exact hf y hy
  rw [toReal_volume_boxSet] at hbound
  rw [boxAverage_eq_inv_mul_integral, abs_mul, abs_of_pos (inv_pos.mpr hvol)]
  calc (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹ * |∫ y in boxSet n x, f y|
      ≤ (((3 : ℝ) ^ (n : ℝ)) ^ d)⁻¹ * (C * ((3 : ℝ) ^ (n : ℝ)) ^ d) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hvol.le)
        rw [← Real.norm_eq_abs]
        exact hbound
    _ = C := by field_simp

/-! ## 3. Triadic cubes are translated boxes -/

/-- **Every `CoarseGraining` cube average is a box average at the cube's centre.** -/
theorem cubeAverage_eq_boxAverage (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q f = boxAverage Q.scale (cubeCenter Q) f := by
  have hrad : boxRadius Q.scale = cubeRadius Q := by
    rw [boxRadius_def, three_rpow_scale_eq Q]
    simp only [cubeRadius]
    ring
  rw [boxAverage_def, hrad, closedBallAverage_eq_setAverage _ (cubeRadius_pos Q).le,
    cubeAverage_eq_setAverage_closedBall]

theorem cubeAverageVec_eq_boxAverageVec (Q : TriadicCube d) (F : Vec d → Vec d) :
    cubeAverageVec Q F = boxAverageVec Q.scale (cubeCenter Q) F := by
  funext i
  exact cubeAverage_eq_boxAverage Q _

/-! ## 4. The translate-uniform negative gauge -/

/-- **The translate-uniform negative gauge of order `-s` on the scales
`n ≤ m`.**

This is the manuscript's `(∞,∞)` negative Besov gauge with the inner maximum
taken over *all* translates of the scale-`n` box rather than over the
triadic grid alone.  It is the carrier the mollifier calculus runs on: a
mollifier centred at `x` averages against `x + □_n`, and no grid cube is
available at a general centre. -/
def UniformBoxGaugeBound (m : ℤ) (s A : ℝ) (F : Vec d → Vec d) : Prop :=
  ∀ n : ℤ, n ≤ m → ∀ x : Vec d, ‖boxAverageVec n x F‖ ≤ A * (3 : ℝ) ^ (-((n : ℝ) * s))

theorem uniformBoxGaugeBound_def (m : ℤ) (s A : ℝ) (F : Vec d → Vec d) :
    UniformBoxGaugeBound m s A F ↔
      ∀ n : ℤ, n ≤ m → ∀ x : Vec d,
        ‖boxAverageVec n x F‖ ≤ A * (3 : ℝ) ^ (-((n : ℝ) * s)) := Iff.rfl

/-- The gauge constant of a nonvacuous gauge is nonnegative. -/
theorem UniformBoxGaugeBound.nonneg {m : ℤ} {s A : ℝ} {F : Vec d → Vec d}
    (h : UniformBoxGaugeBound m s A F) : 0 ≤ A := by
  have hle := h m le_rfl 0
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-((m : ℝ) * s)) := three_rpow_pos _
  have h0 : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-((m : ℝ) * s)) :=
    le_trans (norm_nonneg (boxAverageVec (d := d) m 0 F)) hle
  by_contra hA
  push_neg at hA
  have hneg : A * (3 : ℝ) ^ (-((m : ℝ) * s)) < 0 := mul_neg_of_neg_of_pos hA hpos
  linarith only [h0, hneg]

/-- The gauge is monotone in its constant. -/
theorem UniformBoxGaugeBound.mono {m : ℤ} {s A A' : ℝ} {F : Vec d → Vec d}
    (h : UniformBoxGaugeBound m s A F) (hAA : A ≤ A') : UniformBoxGaugeBound m s A' F := by
  intro n hn x
  exact (h n hn x).trans (mul_le_mul_of_nonneg_right hAA (three_rpow_nonneg _))

/-- The Euclidean norm of a vector is at most `√d` times its sup norm. -/
theorem sqrt_vecNormSq_le (v : Vec d) : Real.sqrt (vecNormSq v) ≤ Real.sqrt d * ‖v‖ := by
  have hsum : vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    have hterm : ∀ i : Fin d, v i * v i ≤ ‖v‖ ^ 2 := by
      intro i
      have hi : |v i| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      have habs : (0 : ℝ) ≤ |v i| := abs_nonneg _
      calc v i * v i = |v i| * |v i| := by rw [← abs_mul, abs_mul_self]
        _ ≤ ‖v‖ * ‖v‖ := mul_le_mul hi hi habs (norm_nonneg _)
        _ = ‖v‖ ^ 2 := by ring
    have hle := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hterm i
    simpa only [vecNormSq, vecDot, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hle
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc Real.sqrt (vecNormSq v) ≤ Real.sqrt ((d : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ‖v‖ := by
        rw [Real.sqrt_mul hd, Real.sqrt_sq (norm_nonneg v)]

/-- **The comparison with the grid gauge.**

A translate-uniform bound `A` at order `-s` on the scales `n ≤ Q.scale` gives
the `(∞,∞)` grid gauge of `HomLiftNegativeNorm` at `√d · A · 3^{-s·Q.scale}` —
the manuscript's scale-normalized left-hand quantity.  The `√d` is the
sup-norm/Euclidean-norm conversion (`CoarseGraining`'s negative Besov family
measures the average vector in the Euclidean norm) and the factor
`3^{-s·Q.scale}` is the normalization of
`negBesovInftyDepthSeminorm_eq_scaleNormalized`.

Only this direction is elementary; see the module docstring. -/
theorem negBesovInftyNorm_le_of_uniformBoxGauge (Q : TriadicCube d) {s A : ℝ}
    {F : Vec d → Vec d} (h : UniformBoxGaugeBound Q.scale s A F) :
    negBesovInftyNorm Q s F ≤ Real.sqrt d * A * (3 : ℝ) ^ (-(s * ((Q.scale : ℤ) : ℝ))) := by
  have hA : 0 ≤ A := h.nonneg
  have hconst : (0 : ℝ) ≤ Real.sqrt d * A * (3 : ℝ) ^ (-(s * ((Q.scale : ℤ) : ℝ))) := by
    have h1 := three_rpow_nonneg (-(s * ((Q.scale : ℤ) : ℝ)))
    have hsd : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg hsd hA) h1
  refine negBesovInftyNorm_le Q s F hconst ?_
  intro j
  have hmax : negBesovInftyDepthMax Q F j
      ≤ Real.sqrt d * A * (3 : ℝ) ^ (-(((Q.scale - (j : ℤ) : ℤ) : ℝ) * s)) := by
    refine negBesovInftyDepthMax_le ?_
    intro R hR
    have hscale : R.scale = Q.scale - (j : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hle : ‖boxAverageVec R.scale (cubeCenter R) F‖
        ≤ A * (3 : ℝ) ^ (-(((R.scale : ℤ) : ℝ) * s)) := by
      refine h R.scale ?_ _
      rw [hscale]
      omega
    calc Real.sqrt (vecNormSq (cubeAverageVec R F))
        ≤ Real.sqrt d * ‖cubeAverageVec R F‖ := sqrt_vecNormSq_le _
      _ = Real.sqrt d * ‖boxAverageVec R.scale (cubeCenter R) F‖ := by
          rw [cubeAverageVec_eq_boxAverageVec]
      _ ≤ Real.sqrt d * (A * (3 : ℝ) ^ (-(((R.scale : ℤ) : ℝ) * s))) :=
          mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
      _ = Real.sqrt d * A * (3 : ℝ) ^ (-(((Q.scale - (j : ℤ) : ℤ) : ℝ) * s)) := by
          rw [hscale, mul_assoc]
  have hweight : (3 : ℝ) ^ (-s * (j : ℝ)) *
      ((3 : ℝ) ^ (-(((Q.scale - (j : ℤ) : ℤ) : ℝ) * s)))
        = (3 : ℝ) ^ (-(s * ((Q.scale : ℤ) : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  calc negBesovInftyDepthSeminorm Q s F j
      = (3 : ℝ) ^ (-s * (j : ℝ)) * negBesovInftyDepthMax Q F j := rfl
    _ ≤ (3 : ℝ) ^ (-s * (j : ℝ)) *
        (Real.sqrt d * A * (3 : ℝ) ^ (-(((Q.scale - (j : ℤ) : ℤ) : ℝ) * s))) :=
        mul_le_mul_of_nonneg_left hmax (three_rpow_nonneg _)
    _ = Real.sqrt d * A * (3 : ℝ) ^ (-(s * ((Q.scale : ℤ) : ℝ))) := by
        rw [← hweight]; ring

end

end Algsuperdiff.Section4.Provider.Homogenization
