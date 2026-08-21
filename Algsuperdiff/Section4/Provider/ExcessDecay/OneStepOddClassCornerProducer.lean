/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerFinal

/-!
# The corner producer: one leg

The corner sibling of `OneStepBoundaryFull.exists_gradientHolder_boundary_faceOdd`:
at a window meeting two upper faces, the boundary gradient-Hölder producer has
a **single leg** — the interior display at the boundary, with no boundary-datum
contribution.  The odd-class defect at the corner datum `(0,0)` (the only
member of the collapsed class) is folded into the excess by the corner pricing
`(★★)` of `OneStepOddClassCornerFinal`.

This is the exact consumer shape the K-package chain
(`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` through
`exists_gradientHolder_boundary_odd_ae`) expects, so the corner regime now
composes with the proved one-step contraction the same way the one-face regime
does.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The zero datum belongs to the odd affine class at every met
configuration. -/
theorem isOddAffineData_zero (x : Vec d) (m k : ℤ) :
    IsOddAffineData x m k (0 : ℝ) (0 : Vec d) := by
  have hlift : ∀ y : Vec d, affineLift x (0 : ℝ) (0 : Vec d) y = 0 := by
    intro y
    show (0 : ℝ) + vecDot (0 : Vec d) (y - x) = 0
    have hv0 : vecDot (0 : Vec d) (y - x) = 0 := by
      show ∑ l, (0 : Vec d) l * (y - x) l = 0
      refine Finset.sum_eq_zero fun l _ => ?_
      show (0 : ℝ) * (y - x) l = 0
      ring
    rw [hv0]
    ring
  exact ⟨fun i _ y _ => hlift y, fun i _ y _ => hlift y⟩

/-- **The corner producer at a met-set-odd competitor: one leg.**

`exists_gradientHolder_boundary_odd_ae` at the corner datum `(0,0)`, the
resulting degenerate odd-class defect folded into the excess by the corner
pricing `(★★)`. -/
theorem exists_gradientHolder_boundary_corner (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i j : Fin d) (V : Vec d → ℝ)
      (c : ℝ) (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m → i ≠ j →
      MeetsUpperFace x m (n - 2) i → MeetsUpperFace x m (n - 2) j →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ l, IntegrableOn (fun p => gradField V p l)
          (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K
          (gradField V) ∧
        K ≤ C * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V := by
  obtain ⟨Cd, hCd0, hCd⟩ := exists_oddClassDefect_le_affineExcessRaw_corner d
  refine ⟨(1 + Cd) * boundaryOddSchauderConst d,
    mul_nonneg (by linarith only [hCd0]) (boundaryOddSchauderConst_nonneg d), ?_⟩
  intro m n x i j V c A hx hmn hij hupi hupj hupV hlowV hharm hVR hmin
  have hVO : V =ᵐ[volume.restrict (reflectedWindow x m (n - 2))]
      fun y => V y + 0 := by
    filter_upwards with y
    ring
  have hOodd : oddExtend x m (n - 2) V
      =ᵐ[volume.restrict (reflectedWindow x m (n - 2))] V :=
    MeasureTheory.ae_restrict_of_ae
      (oddExtend_ae_eq_self_of_faceOdd_forall hmn
        (fun l hl => hupV l hl) (fun l hl => hlowV l hl))
  have hodd : IsOddAffineData x m (n - 2) ((0 : ℝ) - 0) (0 : Vec d) := by
    rw [sub_zero]
    exact isOddAffineData_zero x m (n - 2)
  obtain ⟨K, hK, hint, hgrad, hhol, hbound⟩ :=
    exists_gradientHolder_boundary_odd_ae hd hx hmn hVO hOodd hodd hharm hVR
  refine ⟨K, hK, hint, hgrad, hhol, le_trans hbound ?_⟩
  set kappa : ℝ := boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
    with hkappadef
  have hkappa0 : 0 ≤ kappa := by
    rw [hkappadef]
    exact mul_nonneg (boundaryOddSchauderConst_nonneg d)
      (Real.rpow_nonneg (zpow_pos (by norm_num) (-n)).le _)
  have hscale : (0 : ℝ) < (3 : ℝ) ^ (-(n - 2)) := zpow_pos (by norm_num) _
  have hnormz : (3 : ℝ) ^ (-(n - 2)) * affineExcessRaw (truncatedWindow x m (n - 2)) V
      ≤ affineExcess (truncatedWindow x m (n - 2)) V := by
    rw [affineExcess]
    exact mul_le_mul_of_nonneg_right
      (rpow_volume_truncatedWindow_bounds hd x hx (by omega)).1
      (affineExcessRaw_nonneg _ _)
  have hdefect := hCd m n x i j V c A hx hmn hij hupi hupj hupV hlowV hharm hVR hmin
  have hstep : (3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V 0 0
      ≤ Cd * affineExcess (truncatedWindow x m (n - 2)) V := by
    calc (3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V 0 0
        ≤ (3 : ℝ) ^ (-(n - 2))
            * (Cd * affineExcessRaw (truncatedWindow x m (n - 2)) V) :=
          mul_le_mul_of_nonneg_left hdefect hscale.le
      _ = Cd * ((3 : ℝ) ^ (-(n - 2))
            * affineExcessRaw (truncatedWindow x m (n - 2)) V) := by ring
      _ ≤ Cd * affineExcess (truncatedWindow x m (n - 2)) V :=
          mul_le_mul_of_nonneg_left hnormz hCd0
  have hfold : kappa * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V 0 0)
      ≤ kappa * (Cd * affineExcess (truncatedWindow x m (n - 2)) V) :=
    mul_le_mul_of_nonneg_left hstep hkappa0
  have hrewrite : (1 + Cd) * boundaryOddSchauderConst d
        * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * affineExcess (truncatedWindow x m (n - 2)) V
      = kappa * affineExcess (truncatedWindow x m (n - 2)) V
        + kappa * (Cd * affineExcess (truncatedWindow x m (n - 2)) V) := by
    rw [hkappadef]
    ring
  rw [hrewrite]
  linarith only [hfold]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The one-step excess-decay contraction at a corner window, with the
Schauder slot discharged and no boundary-datum leg.**

The corner sibling of
`excessDecay_oneStep_boundary_faceOdd_of_harmonicApprox`: the competitor is
odd about every met face, the window meets two upper faces, and the corner
odd-class defect has been folded into the excess leg by `(★★)`.  The binders
`hmem`/`hB`/`hharm` and the model, scale and window parameters are transcribed
verbatim from `OneStepConditional.excessDecay_oneStep_of_harmonicApprox`. -/
theorem excessDecay_oneStep_boundary_corner_of_harmonicApprox (d : ℕ) [NeZero d]
    (hd : d ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n : ℤ} {k : ℕ} (_hk : 3 ≤ k) {M : ABKModel d} {s : ℝ}
      (hs : 0 < s) (_hs1 : s ≤ 1) {delta : ℝ} (_hdelta1 : delta ≤ 1) {x z : Vec d}
      {i j : Fin d} (_hx : x ∈ openCubeSet (originCube d m)) (_hnm : n - 1 ≤ m)
      (_hmn : n - 2 < m) (_hij : i ≠ j) (_hupi : MeetsUpperFace x m (n - 2) i)
      (_hupj : MeetsUpperFace x m (n - 2) j)
      {u v : Vec d → ℝ} {c : ℝ} {A : Vec d}
      (_hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
      (_hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
      (_hvR : MemLp v 2 (volume.restrict (reflectedWindow x m (n - 2))))
      (_huv : MemLp (fun y => u y - v y) 2
        (volume.restrict (movedReplacementCube x m n)))
      (_hupv : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ y : Vec d,
        v (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y)
      (_hlowv : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ y : Vec d,
        v (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v y)
      (_hharmclass : HarmonicOnNhd
        (v ∘ (Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
          reflectedWindow x m (n - 2)))
      (_hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) v (c - vecDot A x) A)
      {omega : Cutoff.CutoffSample d}
      (_hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta))
      {B : ℝ≥0∞} (_hB : B ≠ ⊤)
      (_hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B),
      affineExcess (truncatedWindow x m (n - (k : ℤ))) u
        ≤ taylorContractionConst d * C * windowRatioConst d 2
              * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m n) u
          + triangleRemainderConst d C k
              * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal)) := by
  obtain ⟨C, hC0, hC⟩ := Schauder.exists_gradientHolder_boundary_corner d hd
  refine ⟨C, hC0, ?_⟩
  intro m n k hk M s hs hs1 delta hdelta1 x z i j hx hnm hmn hij hupi hupj u v c A
    hu hv hvR huv hupv hlowv hharmclass hmin omega hmem B hB hharm
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    hC m n x i j v c A hx hmn hij hupi hupj hupv hlowv hharmclass hvR hmin
  have hmain := excessDecay_oneStep_of_harmonicApprox hd hk hs hs1 hdelta1 hx hnm hu hv
    huv hmem hB hharm hK hC0 hint hgrad hhol (Kh := 0) (by linarith only [hschauder])
  simpa using hmain

end

end Algsuperdiff.Section4.Provider.ExcessDecay
