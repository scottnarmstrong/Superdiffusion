/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryEndpoint
import Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionSobolevL2

/-!
# The boundary datum leg through the odd class

`OneStepBoundaryDatum` prices the boundary branch's Schauder bound against the
*far-side* seminorm `boundaryDatumLeg`, an object with no direct manuscript
counterpart.  This module replaces it by the sharper and much more meaningful
**odd-class defect**, using the repository's own odd-extension calculus
(`OddReflectionMap`, `OddReflectionSobolevL2`).

## The mechanism

Two proved facts do all the work.

* `OddReflectionMap.oddExtend_affineLift` — an affine function of the **odd
  class** `𝕃_odd(V)` (`IsOddAffineData`: it vanishes on every hyperplane
  carrying a met face of `∂□_m`) is its own partial odd extension.  This is the
  paper's own free parameter `ℓ` in `e.v0.hessian`, i.e. the "affine shift
  freedom" of the excess, restricted to the class that survives the reflection.
* `OddReflectionSobolevL2.eLpNorm_oddExtend_le` — the partial odd extension costs
  at most `2^d` in `L²`, by the cellwise change of variables.

Together with `oddExtend_sub`: if the competitor `V` is **odd** about the met
faces (`oddExtend x m (n-2) V = V`, which is exactly what the odd extension of a
window competitor delivers) and `ℓ ∈ 𝕃_odd`, then `V − ℓ` is again odd, so

```text
  E_raw(V, reflectedWindow) ≤ ‖V − ℓ‖_{L̲²(reflectedWindow)}
                            ≤ 2^d ‖V − ℓ‖_{L̲²(U_2)} = 2^d · affineDistOn U_2 V ℓ .
```

## The residue, isolated to one scalar

```text
  Csch = boundaryOddSchauderConst d = 2^d · boundarySchauderConst d ,
  K_h  = boundaryOddSchauderConst d · (3^{-n})^{1/2} · (3^{-(n-2)} · oddClassDefect) .
```

`oddClassDefect x m n V c A` is the amount by which restricting the affine
competitor to the odd class `𝕃_odd(V)` degrades the excess minimum on `U_2`.  It
is `≥ 0` always, and it is `0` on the interior branch, where
`isOddAffineData_of_no_met_face` makes the odd class the full affine class (so a
minimizer may be chosen inside it).

```text
  oddClassDefect x m n V c A  ≤  C(d) · (3^{n-2})^{3/2} · [∇h]_{C^{0,1/2}(U_2)} ,
```

whose units are exactly right: multiplied by the display's prefactor
`boundaryOddSchauderConst d · (3^{-n})^{1/2} · 3^{-(n-2)}` it yields
`C(d)·[∇h]_{C^{0,1/2}(U_2)}`, the manuscript's second leg, including its
indicator, which is carried here by the vanishing of the defect in the unmet
case.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot axisCube openCubeSet originCube)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two affine parametrizations -/

/-- `affineLift x c A` is the `affineEval` competitor with intercept
`c − A·x`. -/
theorem affineEval_eq_affineLift (x : Vec d) (c : ℝ) (A : Vec d) :
    affineEval (c - vecDot A x) A = affineLift x c A := by
  funext y
  rw [affineEval, affineLift, vecDot_sub_right]
  ring

/-! ## 2. Affine competitors are square integrable on both windows -/

theorem memLp_affineEval_reflectedWindow (x : Vec d) (m k : ℤ) (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict (reflectedWindow x m k)) := by
  refine memLp_affineEval_of_sandwich (zout := fun _ => -(1 / 2) * (3 : ℝ) ^ (m + 2))
    (Lout := (3 : ℝ) ^ (m + 2)) (zpow_pos (by norm_num) (m + 2))
    (measurableSet_reflectedWindow x m k) ?_ c g
  refine subset_trans (reflectedWindow_subset_openCubeSet x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube]

theorem memLp_affineEval_truncatedWindow (x : Vec d) (m k : ℤ) (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict (truncatedWindow x m k)) := by
  refine memLp_affineEval_of_sandwich (zout := x + fun _ => -(1 / 2) * (3 : ℝ) ^ k)
    (Lout := (3 : ℝ) ^ k) (zpow_pos (by norm_num) k)
    (measurableSet_truncatedWindow x m k) ?_ c g
  refine subset_trans (truncatedWindow_subset_translate x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube, image_add_axisCube]

/-! ## 3. The `L²` cost of the odd extension, normalized -/

/-- **The odd extension costs at most `2^d` in the normalized seminorm.**  The
unnormalized `L²` cost is `OddReflectionSobolevL2.eLpNorm_oddExtend_le`; the
normalizers only help, because `|U_2| ≤ |reflectedWindow|`. -/
theorem normalizedL2On_oddExtend_le (x : Vec d) {m k : ℤ} (hkm : k < m) (f : Vec d → ℝ)
    (hRpos : 0 < (volume (reflectedWindow x m k)).toReal)
    (hUpos : 0 < (volume (truncatedWindow x m k)).toReal)
    (hfR : MemLp (oddExtend x m k f) 2 (volume.restrict (reflectedWindow x m k)))
    (hfU : MemLp f 2 (volume.restrict (truncatedWindow x m k))) :
    normalizedL2On (reflectedWindow x m k) (oddExtend x m k f)
      ≤ 2 ^ d * normalizedL2On (truncatedWindow x m k) f := by
  have hUle : (volume (truncatedWindow x m k)).toReal
      ≤ (volume (reflectedWindow x m k)).toReal :=
    ENNReal.toReal_mono (volume_reflectedWindow_ne_top x m k)
      (volume_truncatedWindow_le_volume_reflectedWindow x m k)
  have hc : ((2 : ℝ≥0∞) ^ d).toReal = (2 : ℝ) ^ d := by
    rw [ENNReal.toReal_pow]
    norm_num
  have hfin : (2 : ℝ≥0∞) ^ d * eLpNorm f 2 (volume.restrict (truncatedWindow x m k)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hfU.eLpNorm_ne_top
  have htoReal := ENNReal.toReal_mono hfin (eLpNorm_oddExtend_le x hkm f)
  rw [ENNReal.toReal_mul, hc,
    toReal_eLpNorm_eq_sqrt_volume_mul_normalizedL2On hUpos hfU] at htoReal
  set N : ℝ := normalizedL2On (truncatedWindow x m k) f with hNdef
  have hNnn : 0 ≤ N := normalizedL2On_nonneg _ _
  have hsqR : 0 < Real.sqrt ((volume (reflectedWindow x m k)).toReal) := Real.sqrt_pos.2 hRpos
  have hsq : Real.sqrt ((volume (truncatedWindow x m k)).toReal)
      ≤ Real.sqrt ((volume (reflectedWindow x m k)).toReal) := Real.sqrt_le_sqrt hUle
  have hfacnn : (0 : ℝ) ≤ 2 ^ d * N := mul_nonneg (by positivity) hNnn
  rw [normalizedL2On_eq_toReal_eLpNorm_div hfR, div_le_iff₀ hsqR]
  calc (eLpNorm (oddExtend x m k f) 2 (volume.restrict (reflectedWindow x m k))).toReal
      ≤ 2 ^ d * (Real.sqrt ((volume (truncatedWindow x m k)).toReal) * N) := htoReal
    _ = 2 ^ d * N * Real.sqrt ((volume (truncatedWindow x m k)).toReal) := by ring
    _ ≤ 2 ^ d * N * Real.sqrt ((volume (reflectedWindow x m k)).toReal) :=
        mul_le_mul_of_nonneg_left hsq hfacnn

/-! ## 4. The odd bridge -/

/-- **The odd bridge.**  For a competitor that is odd about the met faces and an
affine competitor of the odd class, the excess minimum on the doubled window is
at most `2^d` times the affine distance on `U_2`. -/
theorem affineExcessRaw_reflectedWindow_le_odd {m k : ℤ} {x : Vec d} (hkm : k < m)
    {V : Vec d → ℝ} (hVodd : oddExtend x m k V = V)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m k c A)
    (hRpos : 0 < (volume (reflectedWindow x m k)).toReal)
    (hUpos : 0 < (volume (truncatedWindow x m k)).toReal)
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m k)))
    (hVU : MemLp V 2 (volume.restrict (truncatedWindow x m k))) :
    affineExcessRaw (reflectedWindow x m k) V
      ≤ 2 ^ d * affineDistOn (truncatedWindow x m k) V (c - vecDot A x) A := by
  set c' : ℝ := c - vecDot A x with hc'def
  have haff : oddExtend x m k (affineEval c' A) = affineEval c' A := by
    rw [hc'def, affineEval_eq_affineLift]
    exact oddExtend_affineLift hodd
  have hfun : oddExtend x m k (fun y => V y - affineEval c' A y)
      = fun y => V y - affineEval c' A y := by
    rw [oddExtend_sub, haff, hVodd]
  have hmemR : MemLp (fun y => V y - affineEval c' A y) 2
      (volume.restrict (reflectedWindow x m k)) :=
    hVR.sub (memLp_affineEval_reflectedWindow x m k c' A)
  have hmemU : MemLp (fun y => V y - affineEval c' A y) 2
      (volume.restrict (truncatedWindow x m k)) :=
    hVU.sub (memLp_affineEval_truncatedWindow x m k c' A)
  have hkey := normalizedL2On_oddExtend_le x hkm (fun y => V y - affineEval c' A y)
    hRpos hUpos (by rw [hfun]; exact hmemR) hmemU
  rw [hfun] at hkey
  refine le_trans (affineExcessRaw_le_affineDistOn _ _ c' A) ?_
  rw [affineDistOn, affineDistOn]
  exact hkey

/-! ## 5. The odd-class defect -/

/-- **The odd-class defect.**  The amount by which restricting the affine
competitor to the odd class `𝕃_odd(V)` degrades the excess minimum on
`U_2 = (x + □_{n-2}) ∩ □_m`.  It is the Lean surface's boundary datum leg. -/
def oddClassDefect (x : Vec d) (m n : ℤ) (V : Vec d → ℝ) (c : ℝ) (A : Vec d) : ℝ :=
  affineDistOn (truncatedWindow x m (n - 2)) V (c - vecDot A x) A
    - affineExcessRaw (truncatedWindow x m (n - 2)) V

theorem oddClassDefect_nonneg (x : Vec d) (m n : ℤ) (V : Vec d → ℝ) (c : ℝ) (A : Vec d) :
    0 ≤ oddClassDefect x m n V c A := by
  rw [oddClassDefect, sub_nonneg]
  exact affineExcessRaw_le_affineDistOn _ _ _ _

/-- **The defect vanishes for a minimizer of the odd class when no face is
met.**  In the interior regime the odd class is the whole affine class
(`isOddAffineData_of_no_met_face`), so an unrestricted minimizer is admissible
and the defect is `0`. -/
theorem oddClassDefect_of_isAffineMinimizer {x : Vec d} {m n : ℤ} {V : Vec d → ℝ}
    {c : ℝ} {A : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A) :
    oddClassDefect x m n V c A = 0 := by
  rw [oddClassDefect, hmin, sub_self]

/-! ## 6. The constant and the producer -/

/-- The Schauder constant of the boundary branch through the odd class:
`2^d · boundarySchauderConst d`. -/
def boundaryOddSchauderConst (d : ℕ) [NeZero d] : ℝ := 2 ^ d * boundarySchauderConst d

theorem boundaryOddSchauderConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ boundaryOddSchauderConst d :=
  mul_nonneg (by positivity) (boundarySchauderConst_nonneg d)

/-- **The Schauder gradient-Hölder estimate, boundary branch — the producer through the
odd class.**

For an odd competitor `V` classically harmonic on the doubled window and an odd
affine datum `(c,A)`, the four slots `hint / hgrad / hhol / hschauder` of
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` hold with

```text
  Csch = boundaryOddSchauderConst d ,
  K_h  = boundaryOddSchauderConst d · (3^{-n})^{1/2} · (3^{-(n-2)} · oddClassDefect x m n V c A) .
```
-/
theorem exists_gradientHolder_boundary_odd [NeZero d] (hd : d ≠ 0) {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    {V : Vec d → ℝ} (hVodd : oddExtend x m (n - 2) V = V)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) c A)
    (hharm : HarmonicOnNhd (V ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2)))) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField V p i) (truncatedWindow x m (n - 3)) volume) ∧
      HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
      HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K (gradField V) ∧
      K ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m (n - 2)) V
          + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
            * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
  have hintsq : ∀ (c' : ℝ) (g' : Vec d),
      IntegrableOn (fun y => (V y - affineEval c' g' y) ^ 2)
        (reflectedWindow x m (n - 2)) volume :=
    fun c' g' => integrableOn_sub_affineEval_sq_reflectedWindow x hVR c' g'
  obtain ⟨K, hK, hint, hgrad, hhol, hraw⟩ :=
    exists_gradientHolder_boundary_raw hx hmn hharm hintsq
  refine ⟨K, hK, hint, hgrad, hhol, le_trans hraw ?_⟩
  have hVU : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hVR.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m (n - 2)) le_rfl)
  have hRpos : 0 < (volume (reflectedWindow x m (n - 2))).toReal :=
    volume_toReal_reflectedWindow_pos x hx (by omega)
  have hUpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hbridge := affineExcessRaw_reflectedWindow_le_odd (k := n - 2) hmn hVodd hodd
    hRpos hUpos hVR hVU
  have hdist : affineDistOn (truncatedWindow x m (n - 2)) V (c - vecDot A x) A
      = affineExcessRaw (truncatedWindow x m (n - 2)) V + oddClassDefect x m n V c A := by
    rw [oddClassDefect]
    ring
  rw [hdist] at hbridge
  have hscale : (0 : ℝ) < (3 : ℝ) ^ (-(n - 2)) := zpow_pos (by norm_num) _
  have hnormz : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V
      ≤ affineExcess (truncatedWindow x m (n - 2)) V := by
    rw [affineExcess]
    exact mul_le_mul_of_nonneg_right
      (rpow_volume_truncatedWindow_bounds hd x hx (by omega)).1
      (affineExcessRaw_nonneg _ _)
  have hkappa : (0 : ℝ) ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) :=
    mul_nonneg (boundarySchauderConst_nonneg d) (Real.rpow_nonneg (by positivity) _)
  have hstep : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (reflectedWindow x m (n - 2)) V
      ≤ 2 ^ d * affineExcess (truncatedWindow x m (n - 2)) V
        + 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
    have h1 := mul_le_mul_of_nonneg_left hbridge hscale.le
    have h2 : (3 : ℝ) ^ (-(n - 2)) * (2 ^ d * (affineExcessRaw (truncatedWindow x m (n - 2)) V
          + oddClassDefect x m n V c A))
        = 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V)
          + 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by ring
    rw [h2] at h1
    have h3 : (2 : ℝ) ^ d
          * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V)
        ≤ 2 ^ d * affineExcess (truncatedWindow x m (n - 2)) V :=
      mul_le_mul_of_nonneg_left hnormz (by positivity)
    linarith only [h1, h3]
  calc boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * ((3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (reflectedWindow x m (n - 2)) V)
      ≤ boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * (2 ^ d * affineExcess (truncatedWindow x m (n - 2)) V
            + 2 ^ d * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A)) :=
        mul_le_mul_of_nonneg_left hstep hkappa
    _ = boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * affineExcess (truncatedWindow x m (n - 2)) V
        + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
          * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
        rw [boundaryOddSchauderConst]
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The one-step excess-decay contraction on the boundary branch, through the
odd class.**

The manuscript's display with both legs present: the contraction against `E(u,
U_0)`, the harmonic-approximation remainder, and the boundary-datum leg, the
last carried by the single scalar `oddClassDefect x m n v c A` — the odd-class
degradation of the excess minimum on `U_2`, which vanishes whenever a minimizer
may be chosen inside `𝕃_odd` (in particular on the interior branch). -/
theorem excessDecay_oneStep_boundary_odd_of_harmonicApprox [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {k : ℕ} (hk : 3 ≤ k) {M : ABKModel d} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {delta : ℝ}
    (hdelta1 : delta ≤ 1) {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m) (hmn : n - 2 < m)
    {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (hvR : MemLp v 2 (volume.restrict (reflectedWindow x m (n - 2))))
    (huv : MemLp (fun y => u y - v y) 2 (volume.restrict (movedReplacementCube x m n)))
    (hvodd : oddExtend x m (n - 2) v = v)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) c A)
    (hharmclass : HarmonicOnNhd (v ∘ Schauder.toEuc.symm)
      ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
      (s / 8 * Real.sqrt delta))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * boundaryOddSchauderConst d * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d (boundaryOddSchauderConst d) k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
            * (boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n v c A)) := by
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    Schauder.exists_gradientHolder_boundary_odd hd hx hmn hvodd hodd hharmclass hvR
  exact excessDecay_oneStep_of_harmonicApprox hd hk hs hs1 hdelta1 hx hnm hu hv huv hmem hB
    hharm hK (Schauder.boundaryOddSchauderConst_nonneg d) hint hgrad hhol hschauder

end

end Algsuperdiff.Section4.Provider.ExcessDecay
