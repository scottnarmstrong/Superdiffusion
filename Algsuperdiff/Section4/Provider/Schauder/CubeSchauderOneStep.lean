/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepAssembly
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderProducer

/-!
# Cube Schauder: the interior one-step contraction at the Lipschitz rate

The proved `ExcessDecay.excessDecay_oneStep_triangle_of_schauder` contracts at
`C(d)·3^{-k/2}`, which is the same rate as the forcing remainder: `theta/rho =
C(d)` is `k`-independent and larger than `1`, so no gap exists and the
Campanato exponent tops out strictly below `1/2`.  That route cannot reach the
frozen external's inclusive endpoint `s ≤ 1/2`.

This module re-derives the interior one step from the **Lipschitz** atom
`ExcessDecay.gradField_lipschitzOn_of_harmonic` (`α = 1`, the pointwise
`C^{1,1}` estimate for harmonic functions) instead of its `C^{0,1/2}` corollary,
and the contraction factor improves to `C(d)·3^{-k}`:

```text
  E(u, U_k) ≤ C_contr(d) · 3^{-k} · E(u, U_0)
              + C_rem(d,k) · 3^{-n} · ‖u - v‖_{L̲²(U_2)} ,
```

`U_j = (x + □_{n-j}) ∩ □_m`.  Since the remainder decays at `3^{-k/2}` per step
(the freezing gain of a `C^{0,1/2}` forcing), `theta = C_contr(d) 3^{-k}` is
strictly below `rho = 3^{-k/2}` as soon as `C_contr(d) < 3^{k/2}`, and the gap
is then uniform.  That is the resolution the development's rate question
needed; `CubeSchauderCampanato` fixes the step size and runs the iteration.

## Why the exponent improves

A first-order Taylor competitor built from a gradient which is only
`C^{0,1/2}(U)` has residual `K·r^{3/2}` on a window of radius `r`, hence excess
`K·r^{1/2}`; built from a **Lipschitz** gradient it has residual `L·r²`, hence
excess `L·r`.  Feeding the harmonic gradient-Lipschitz bound
`L ≲ 3^{-n} E(v,U_2)` gives `E(v,U_k) ≲ 3^{-n}·3^{n-k}·E(v,U_2) = 3^{-k}E(v,U_2)`
— one full power of the scale instead of a half.

## Main results

* `abs_sub_affineLift_volumeAverage_le_lipschitz` — the mean-value residual
  `2 d L r²` at a Lipschitz gradient field.
* `affineExcess_le_taylorLipschitz` — `E(f,W) ≤ (9d/2) · L · 3^k` on the
  truncated window of scale `k`.
* `exists_gradientLipschitz_interior` — the harmonic gradient-Lipschitz bound in
  the window vocabulary, at `schauderLipschitzWindowConst d · 3^{-n} · E(v,U_2)`.
* `excessDecay_oneStep_lipschitz` — the displayed one-step contraction.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`, display `e.Sch1a.1`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory InnerProductSpace
open Homogenization
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The mean-value residual at a Lipschitz gradient -/

/-- **The affine-lift residual, Lipschitz gradient.**

If `f` has gradient field `G` on the convex window `W` of sup-radius `r` around
`x`, and `G` is `L`-Lipschitz on `W`, then `f` differs from its affine lift at
`x` (built with the *average* gradient) by at most `2 d L r²`.

This is the `α = 1` sibling of
`ExcessDecay.abs_sub_affineLift_volumeAverage_le`, whose `α = 1/2` hypothesis
yields the weaker `2 d K r^{3/2}`. -/
theorem abs_sub_affineLift_volumeAverage_le_lipschitz {W : Set (Vec d)} {f : Vec d → ℝ}
    {G : Vec d → Vec d} {L r : ℝ} {x y : Vec d} (hW : Convex ℝ W) (hx : x ∈ W)
    (hy : y ∈ W) (hL : 0 ≤ L) (hr0 : 0 ≤ r) (hvolpos : 0 < volume W)
    (hvoltop : volume W < ⊤) (hint : ∀ i, IntegrableOn (fun p => G p i) W volume)
    (hf : HasGradientOn W f G)
    (hG : ∀ p ∈ W, ∀ q ∈ W, ‖G p - G q‖ ≤ L * ‖p - q‖)
    (hdiam : ∀ p ∈ W, ‖p - x‖ ≤ r) :
    |f y - affineLift x (f x) (volumeAverageVec W G) y| ≤ 2 * (d : ℝ) * L * r ^ 2 := by
  have hLr : 0 ≤ L * r := mul_nonneg hL hr0
  have hbase : ∀ p ∈ W, ‖G p - G x‖ ≤ L * r := fun p hp =>
    (hG p hp x hx).trans (mul_le_mul_of_nonneg_left (hdiam p hp) hL)
  have havg : ‖volumeAverageVec W G - G x‖ ≤ L * r :=
    norm_volumeAverageVec_sub_le hvolpos hvoltop hint hLr hbase
  have hslope : ∀ p ∈ W, ‖G p - volumeAverageVec W G‖ ≤ 2 * (L * r) := by
    intro p hp
    have htri : ‖G p - volumeAverageVec W G‖ ≤
        ‖G p - G x‖ + ‖G x - volumeAverageVec W G‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub (G p) (G x) (volumeAverageVec W G)
    have hsymm : ‖G x - volumeAverageVec W G‖ = ‖volumeAverageVec W G - G x‖ :=
      norm_sub_rev _ _
    rw [hsymm] at htri
    linarith only [htri, hbase p hp, havg]
  have hmain := abs_sub_affineLift_le (f := f) (G := G) (A := volumeAverageVec W G)
    hW hx hy (by linarith only [hLr] : (0 : ℝ) ≤ 2 * (L * r)) hf hslope (hdiam y hy)
  refine hmain.trans (le_of_eq ?_)
  ring

/-! ## 2. The Lipschitz affine competitor on a truncated window -/

/-- The raw Lipschitz Taylor bound on the truncated window of scale `k`. -/
theorem affineExcessRaw_le_taylorLipschitz {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {f : Vec d → ℝ}
    {G : Vec d → Vec d} {L : ℝ} (hL : 0 ≤ L)
    (hmem : MemLp f 2 (volume.restrict (truncatedWindow x m k)))
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hf : HasGradientOn (truncatedWindow x m k) f G)
    (hG : ∀ p ∈ truncatedWindow x m k, ∀ q ∈ truncatedWindow x m k,
      ‖G p - G q‖ ≤ L * ‖p - q‖) :
    affineExcessRaw (truncatedWindow x m k) f
      ≤ 2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2 := by
  have hMnn : (0 : ℝ) ≤ 2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2 := by positivity
  have hxW : x ∈ truncatedWindow x m k := mem_truncatedWindow_self k hx
  have hbound : ∀ y ∈ truncatedWindow x m k,
      |f y - affineEval (f x - vecDot (volumeAverageVec (truncatedWindow x m k) G) x)
          (volumeAverageVec (truncatedWindow x m k) G) y|
        ≤ 2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2 := by
    intro y hy
    have h := abs_sub_affineLift_volumeAverage_le_lipschitz (W := truncatedWindow x m k)
      (f := f) (G := G) (L := L) (r := (3 : ℝ) ^ k / 2) (x := x) (y := y)
      (convex_truncatedWindow x m k) hxW hy hL (by positivity)
      (volume_truncatedWindow_pos k hx) (volume_truncatedWindow_lt_top x m k) hint hf hG
      (fun p hp => norm_sub_le_of_mem_truncatedWindow hp)
    rwa [affineLift_eq_affineEval] at h
  refine le_trans (affineExcessRaw_le_affineDistOn (truncatedWindow x m k) f
    (f x - vecDot (volumeAverageVec (truncatedWindow x m k) G) x)
    (volumeAverageVec (truncatedWindow x m k) G)) ?_
  rw [affineDistOn]
  exact normalizedL2On_le_of_abs_le (measurableSet_truncatedWindow x m k)
    (volume_toReal_truncatedWindow_pos x hx hkm)
    (ne_of_lt (volume_truncatedWindow_lt_top x m k)) hMnn
    (integrableOn_sub_affineEval_sq_truncatedWindow x hmem _ _) hbound

/-- The constant of the Lipschitz affine competitor: `9 d / 2`, the product of
the truncated normalizer's slack `9` and the mean-value factor `d/2`. -/
def taylorLipschitzConst (d : ℕ) : ℝ := 9 / 2 * (d : ℝ)

theorem taylorLipschitzConst_nonneg (d : ℕ) : 0 ≤ taylorLipschitzConst d := by
  rw [taylorLipschitzConst]
  positivity

/-- **The Lipschitz affine competitor, excess form.**

`E(f, (x+□_k) ∩ □_m) ≤ (9d/2) · L · 3^k` for `f` whose gradient field is
`L`-Lipschitz on the window.  One full power of the scale — the improvement over
`ExcessDecay.affineExcess_le_taylor`'s half power. -/
theorem affineExcess_le_taylorLipschitz (hd : d ≠ 0) {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {f : Vec d → ℝ}
    {G : Vec d → Vec d} {L : ℝ} (hL : 0 ≤ L)
    (hmem : MemLp f 2 (volume.restrict (truncatedWindow x m k)))
    (hint : ∀ i, IntegrableOn (fun p => G p i) (truncatedWindow x m k) volume)
    (hf : HasGradientOn (truncatedWindow x m k) f G)
    (hG : ∀ p ∈ truncatedWindow x m k, ∀ q ∈ truncatedWindow x m k,
      ‖G p - G q‖ ≤ L * ‖p - q‖) :
    affineExcess (truncatedWindow x m k) f ≤ taylorLipschitzConst d * L * (3 : ℝ) ^ k := by
  obtain ⟨_, hnorm⟩ := rpow_volume_truncatedWindow_bounds hd x hx hkm
  have hraw := affineExcessRaw_le_taylorLipschitz hx hkm hL hmem hint hf hG
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  calc affineExcess (truncatedWindow x m k) f
      = ((volume (truncatedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) *
          affineExcessRaw (truncatedWindow x m k) f := rfl
    _ ≤ (9 * (3 : ℝ) ^ (-k)) * (2 * (d : ℝ) * L * ((3 : ℝ) ^ k / 2) ^ 2) :=
        mul_le_mul hnorm hraw (affineExcessRaw_nonneg _ _) (by positivity)
    _ = taylorLipschitzConst d * L * (3 : ℝ) ^ k := by
        rw [taylorLipschitzConst, zpow_neg]
        field_simp

/-! ## 3. The harmonic gradient-Lipschitz bound, in the window vocabulary -/

/-- **The Lipschitz Schauder constant of the interior branch.**  `C(d)` explicit:
`1296 · schauderConst d · schauderRatioConst d`, where `1296 = 4 · 324` collects
the atom's factor `4`, the half-radius `R = 3^{n-3}/2` and the two triadic scale
gaps `n-3`, `n-2` against `n`. -/
def schauderLipschitzWindowConst (d : ℕ) [NeZero d] : ℝ :=
  1296 * schauderConst d * schauderRatioConst d

theorem schauderLipschitzWindowConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ schauderLipschitzWindowConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (schauderConst_nonneg d)) (schauderRatioConst_nonneg d)

/-- The scale bookkeeping of the Lipschitz producer:
`(3^{n-3}/2)⁻² · 3^{n-2} = 324 · 3^{-n}`. -/
private theorem lipschitz_scale_identity (n : ℤ) :
    ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (3 : ℝ) ^ (n - 2)
      = 324 * (3 : ℝ) ^ (-n) := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have hnpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have h27 : (3 : ℝ) ^ (-3 : ℤ) = 1 / 27 := by norm_num
  have h9 : (3 : ℝ) ^ (-2 : ℤ) = 1 / 9 := by norm_num
  have hA3 : (3 : ℝ) ^ (n - 3) = (3 : ℝ) ^ n / 27 := by
    rw [show n - 3 = n + (-3 : ℤ) by ring, zpow_add₀ h3ne, h27]
    ring
  have hA2 : (3 : ℝ) ^ (n - 2) = (3 : ℝ) ^ n / 9 := by
    rw [show n - 2 = n + (-2 : ℤ) by ring, zpow_add₀ h3ne, h9]
    ring
  rw [hA3, hA2, zpow_neg]
  field_simp
  ring

/-- **The harmonic gradient-Lipschitz bound on the one-step window.**

For `v` harmonic on the replacement window `(x + □_{n-2}) ∩ □_m` of the interior
branch, the gradient field `gradField v` is Lipschitz on the inner window
`(x + □_{n-3}) ∩ □_m` with constant

```text
  schauderLipschitzWindowConst d · 3^{-n} · E(v, (x+□_{n-2}) ∩ □_m) .
```

This is `ExcessDecay.exists_gradientHolder_interior` with the atom read
at its own exponent `α = 1` instead of the lossy `α = 1/2` corollary. -/
theorem exists_gradientLipschitz_interior [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 3 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {v : Vec d → ℝ}
    (hharm : HarmonicOnNhd (v ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2)))
    (hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (v y - affineEval c g y) ^ 2)
        (truncatedWindow x m (n - 2)) volume) :
    ∀ p ∈ truncatedWindow x m (n - 3), ∀ q ∈ truncatedWindow x m (n - 3),
      ‖gradField v p - gradField v q‖
        ≤ (schauderLipschitzWindowConst d * (3 : ℝ) ^ (-n)
            * affineExcess (truncatedWindow x m (n - 2)) v) * ‖p - q‖ := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 := by linarith only [h3]
  have hR2 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 / 2 := by linarith only [h3]
  have hatom := gradField_lipschitzOn_of_harmonic
    (S := (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2))
    (W := truncatedWindow x m (n - 3)) (W₂ := truncatedWindow x m (n - 2))
    (R := (3 : ℝ) ^ (n - 3) / 2) (ratio := schauderRatioConst d)
    hharm (convex_truncatedWindow x m (n - 3)) hR
    (schauderRatioConst_nonneg d)
    (fun p hp => metricBall_toEuc_subset_image_of_interior hcube hp)
    (fun p hp => euclideanBall_subset_truncatedWindow_of_interior hcube hp hR2
      (by linarith only [h3]))
    (volume_toReal_truncatedWindow_pos x hx (by omega : n - 2 - 1 ≤ m))
    (fun p _ => lt_of_lt_of_le (by positivity) (volume_toReal_euclideanBall_ge p hR2))
    (fun p _ => sqrt_volume_ratio_le hx hnm p)
    hintsq
  -- the excess normalizer on the enveloping window
  set W₂ : Set (Vec d) := truncatedWindow x m (n - 2) with hW₂def
  set E : ℝ := affineExcessRaw W₂ v with hEdef
  set A : ℝ := affineExcess W₂ v with hAdef
  have hEnn : 0 ≤ E := affineExcessRaw_nonneg W₂ v
  have hAnn : 0 ≤ A := affineExcess_nonneg W₂ v
  have hlo : (3 : ℝ) ^ (-(n - 2)) ≤ ((volume W₂).toReal) ^ (-(d : ℝ)⁻¹) := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      exact absurd rfl (NeZero.ne (0 : ℕ))
    · exact (rpow_volume_truncatedWindow_bounds (by omega) x hx (by omega : n - 2 - 1 ≤ m)).1
  have hEA : E ≤ (3 : ℝ) ^ (n - 2) * A := by
    have hstep : (3 : ℝ) ^ (-(n - 2)) * E ≤ A := by
      rw [hAdef, affineExcess]
      exact mul_le_mul_of_nonneg_right hlo hEnn
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hstep hpos.le
    rwa [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel, zpow_zero,
      one_mul] at hmul
  -- the constant comparison
  set C : ℝ := schauderConst d with hCdef
  set ra : ℝ := schauderRatioConst d with hradef
  have hCnn : 0 ≤ C := schauderConst_nonneg d
  have hrann : 0 ≤ ra := schauderRatioConst_nonneg d
  have hRinv : (0 : ℝ) ≤ ((3 : ℝ) ^ (n - 3) / 2)⁻¹ := (inv_nonneg.2 hR.le)
  have hcoef : (0 : ℝ) ≤ 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ra :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCnn) hRinv) hRinv) hrann
  have hkey : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
      ≤ schauderLipschitzWindowConst d * (3 : ℝ) ^ (-n) * A := by
    have hstep : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (ra * E)
        ≤ 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ra
            * ((3 : ℝ) ^ (n - 2) * A) := by
      have h := mul_le_mul_of_nonneg_left hEA hcoef
      linarith only [h]
    refine hstep.trans (le_of_eq ?_)
    have hid := lipschitz_scale_identity n
    have hexp : 4 * C * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ra
          * ((3 : ℝ) ^ (n - 2) * A)
        = 4 * C * ra * A
            * (((3 : ℝ) ^ (n - 3) / 2)⁻¹ * ((3 : ℝ) ^ (n - 3) / 2)⁻¹ * (3 : ℝ) ^ (n - 2)) := by
      ring
    rw [hexp, hid, schauderLipschitzWindowConst, ← hCdef, ← hradef]
    ring
  intro p hp q hq
  refine (hatom p hp q hq).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact hkey

/-! ## 4. The one-step contraction -/

/-- The contraction constant of the Lipschitz one step:
`taylorLipschitzConst d · schauderLipschitzWindowConst d · windowRatioConst d 2`. -/
def lipschitzContractionConst (d : ℕ) [NeZero d] : ℝ :=
  taylorLipschitzConst d * schauderLipschitzWindowConst d * windowRatioConst d 2

theorem lipschitzContractionConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ lipschitzContractionConst d :=
  mul_nonneg (mul_nonneg (taylorLipschitzConst_nonneg d)
    (schauderLipschitzWindowConst_nonneg d)) (windowRatioConst_nonneg d 2)

/-- The remainder constant of the Lipschitz one step: `81 C_taylor C_lip +
9·3^k·√((3^k)^d)`, i.e. the printed `C 3^{(1+d/2)k}`. -/
def lipschitzRemainderConst (d : ℕ) [NeZero d] (k : ℕ) : ℝ :=
  81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
    + 9 * (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d)

theorem lipschitzRemainderConst_nonneg (d : ℕ) [NeZero d] (k : ℕ) :
    0 ≤ lipschitzRemainderConst d k := by
  have h1 : 0 ≤ 81 * taylorLipschitzConst d * schauderLipschitzWindowConst d :=
    mul_nonneg (mul_nonneg (by norm_num) (taylorLipschitzConst_nonneg d))
      (schauderLipschitzWindowConst_nonneg d)
  have h2 : 0 ≤ 9 * (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d) := by positivity
  rw [lipschitzRemainderConst]
  linarith only [h1, h2]

private theorem three_zpow_neg_nat_le_one {k : ℕ} : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := by
  calc (3 : ℝ) ^ (-(k : ℤ)) ≤ (3 : ℝ) ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 := zpow_zero 3

/-- **The interior one-step contraction at the Lipschitz rate.**

For `u` on the window family `U_j = (x + □_{n-j}) ∩ □_m` and `v` harmonic on
`U_2` (in the interior regime `x + □_{n-2} ⊆ □_m`),

```text
  E(u,U_k) ≤ C_contr(d) · 3^{-k} · E(u,U_0)
              + C_rem(d,k) · 3^{-n} · ‖u - v‖_{L̲²(U_2)} .
```

The contraction factor is `3^{-k}`, a **full** power of the step, as against the
`3^{-k/2}` of `ExcessDecay.excessDecay_oneStep_triangle_of_schauder`. -/
theorem excessDecay_oneStep_lipschitz [NeZero d] (hd : d ≠ 0) {m n : ℤ} {k : ℕ}
    (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (hharm : HarmonicOnNhd (v ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2))) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ))
            * affineExcess (truncatedWindow x m n) u
        + lipschitzRemainderConst d k
            * ((3 : ℝ) ^ (-n)
              * normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y)) := by
  have hne : (3 : ℝ) ≠ 0 := by norm_num
  have hCT : 0 ≤ taylorLipschitzConst d := taylorLipschitzConst_nonneg d
  have hCL : 0 ≤ schauderLipschitzWindowConst d := schauderLipschitzWindowConst_nonneg d
  have hkappa : 0 ≤ windowRatioConst d 2 := windowRatioConst_nonneg d 2
  -- window nondegeneracy at the four scales in play
  have hmk : n - (k : ℤ) - 1 ≤ m := by omega
  have hm3 : n - 3 - 1 ≤ m := by omega
  have hm2 : n - 2 - 1 ≤ m := by omega
  -- window inclusions and the restricted `MemLp` slots
  have hsub_k3 : truncatedWindow x m (n - (k : ℤ)) ⊆ truncatedWindow x m (n - 3) :=
    truncatedWindow_mono x m (by omega)
  have hsub_32 : truncatedWindow x m (n - 3) ⊆ truncatedWindow x m (n - 2) :=
    truncatedWindow_mono x m (by omega)
  have hsub_20 : truncatedWindow x m (n - 2) ⊆ truncatedWindow x m n :=
    truncatedWindow_mono x m (by omega)
  have huk : MemLp u 2 (volume.restrict (truncatedWindow x m (n - (k : ℤ)))) :=
    memLp_restrict_of_subset (hsub_k3.trans (hsub_32.trans hsub_20)) hu
  have hvk : MemLp v 2 (volume.restrict (truncatedWindow x m (n - (k : ℤ)))) :=
    memLp_restrict_of_subset (hsub_k3.trans (hsub_32.trans hsub_20)) hv
  have hu2 : MemLp u 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset hsub_20 hu
  have hv2 : MemLp v 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset hsub_20 hv
  have hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (v y - affineEval c g y) ^ 2)
        (truncatedWindow x m (n - 2)) volume :=
    fun c g => integrableOn_sub_affineEval_sq_truncatedWindow x hv2 c g
  -- the four producer slots
  obtain ⟨_, _, hint, hgrad, _, _⟩ :=
    exists_gradientHolder_interior hd hx (by omega : n - 3 ≤ m) hcube hharm hintsq
  have hlip := exists_gradientLipschitz_interior hx (by omega : n - 3 ≤ m) hcube hharm hintsq
  set Ev2 : ℝ := affineExcess (truncatedWindow x m (n - 2)) v with hEv2def
  set L : ℝ := schauderLipschitzWindowConst d * (3 : ℝ) ^ (-n) * Ev2 with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    exact mul_nonneg (mul_nonneg hCL (zpow_pos (by norm_num) _).le)
      (affineExcess_nonneg _ _)
  -- (1) the triangle step on `U_k`
  have h1 := affineExcess_sub_le_truncatedWindow hd hx hmk huk hvk
  -- (2) the Lipschitz affine competitor on `U_k`
  have h2 := affineExcess_le_taylorLipschitz hd hx hmk hLnn hvk
    (fun i => (hint i).mono_set hsub_k3) (hgrad.mono_set hsub_k3)
    (fun p hp q hq => hlip p (hsub_k3 hp) q (hsub_k3 hq))
  -- (4) the triangle step on `U_2`, with `u` and `v` interchanged
  have h4 := affineExcess_sub_le_truncatedWindow hd hx hm2 hv2 hu2
  rw [normalizedL2On_sub_comm] at h4
  -- (5) quasi-monotonicity `E(u,U_2) ≤ κ E(u,U_0)`
  have h5 : affineExcess (truncatedWindow x m (n - 2)) u
      ≤ windowRatioConst d 2 * affineExcess (truncatedWindow x m n) u := by
    have h := affineExcess_truncatedWindow_le (l := n) x hx hm2 hnm (by omega) hu
    rwa [show n - (n - 2) = (2 : ℤ) by ring] at h
  -- (6) the `L̲²` window transfer
  have h6 : normalizedL2On (truncatedWindow x m (n - (k : ℤ))) (fun y => u y - v y)
      ≤ Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d)
        * normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y) := by
    have h := normalizedL2On_truncatedWindow_le (l := n - 2) (k := n - (k : ℤ)) hx hmk hm2
      (by omega) (f := fun y => u y - v y) (hu2.sub hv2)
    rwa [show n - 2 - (n - (k : ℤ)) + 2 = (k : ℤ) by ring] at h
  -- the two `3`-power rewrites
  have hpow_k : (3 : ℝ) ^ (-(n - (k : ℤ))) = (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) := by
    rw [show -(n - (k : ℤ)) = (k : ℤ) + -n by ring, zpow_add₀ hne]
  have hpow_2 : (3 : ℝ) ^ (-(n - 2)) = 9 * (3 : ℝ) ^ (-n) := by
    rw [show -(n - 2) = (2 : ℤ) + -n by ring, zpow_add₀ hne]
    norm_num
  rw [hpow_k] at h1
  rw [hpow_2] at h4
  -- assemble
  set S2 := normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - v y) with hS2
  set E0 := affineExcess (truncatedWindow x m n) u with hE0
  set R := Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d) with hR
  have hS2nn : 0 ≤ S2 := normalizedL2On_nonneg _ _
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  -- the competitor's excess, folded through the Lipschitz atom
  have hL3 : taylorLipschitzConst d * L * (3 : ℝ) ^ (n - (k : ℤ))
      = taylorLipschitzConst d * schauderLipschitzWindowConst d * (3 : ℝ) ^ (-(k : ℤ)) * Ev2 := by
    rw [hLdef]
    have hmul : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - (k : ℤ)) = (3 : ℝ) ^ (-(k : ℤ)) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    calc taylorLipschitzConst d * (schauderLipschitzWindowConst d * (3 : ℝ) ^ (-n) * Ev2)
          * (3 : ℝ) ^ (n - (k : ℤ))
        = taylorLipschitzConst d * schauderLipschitzWindowConst d
            * ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - (k : ℤ))) * Ev2 := by ring
      _ = taylorLipschitzConst d * schauderLipschitzWindowConst d
            * (3 : ℝ) ^ (-(k : ℤ)) * Ev2 := by rw [hmul]
  rw [hL3] at h2
  -- fold `E(v,U_2)` into `E(u,U_0)` and the remainder
  have hEv2 : Ev2 ≤ windowRatioConst d 2 * E0 + 81 * ((3 : ℝ) ^ (-n) * S2) := by
    linarith only [h4, h5]
  have hcoef : (0 : ℝ) ≤ taylorLipschitzConst d * schauderLipschitzWindowConst d
      * (3 : ℝ) ^ (-(k : ℤ)) :=
    mul_nonneg (mul_nonneg hCT hCL) (zpow_pos (by norm_num) _).le
  have hfold : taylorLipschitzConst d * schauderLipschitzWindowConst d
        * (3 : ℝ) ^ (-(k : ℤ)) * Ev2
      ≤ lipschitzContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) * E0
        + 81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
            * (3 : ℝ) ^ (-(k : ℤ)) * ((3 : ℝ) ^ (-n) * S2) := by
    have h := mul_le_mul_of_nonneg_left hEv2 hcoef
    rw [lipschitzContractionConst]
    linarith only [h]
  -- discard the `3^{-k} ≤ 1` factor on the remainder leg
  have hQnn : (0 : ℝ) ≤ 81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
      * ((3 : ℝ) ^ (-n) * S2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCT) hCL)
      (mul_nonneg h3npos.le hS2nn)
  have hdrop : 81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
        * (3 : ℝ) ^ (-(k : ℤ)) * ((3 : ℝ) ^ (-n) * S2)
      ≤ 81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
          * ((3 : ℝ) ^ (-n) * S2) := by
    calc 81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
          * (3 : ℝ) ^ (-(k : ℤ)) * ((3 : ℝ) ^ (-n) * S2)
        = (81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
            * ((3 : ℝ) ^ (-n) * S2)) * (3 : ℝ) ^ (-(k : ℤ)) := by ring
      _ ≤ (81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
            * ((3 : ℝ) ^ (-n) * S2)) * 1 :=
          mul_le_mul_of_nonneg_left three_zpow_neg_nat_le_one hQnn
      _ = 81 * taylorLipschitzConst d * schauderLipschitzWindowConst d
            * ((3 : ℝ) ^ (-n) * S2) := by ring
  -- the raw `‖u-v‖` leg on `U_k`
  have hraw : 9 * ((3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n))
        * normalizedL2On (truncatedWindow x m (n - (k : ℤ))) (fun y => u y - v y)
      ≤ 9 * (3 : ℝ) ^ (k : ℤ) * R * ((3 : ℝ) ^ (-n) * S2) := by
    have hc : (0 : ℝ) ≤ 9 * ((3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n)) := by positivity
    have h := mul_le_mul_of_nonneg_left h6 hc
    linarith only [h]
  rw [lipschitzRemainderConst]
  linarith only [h1, h2, hfold, hdrop, hraw]

end

end Algsuperdiff.Section4.Provider.Schauder
