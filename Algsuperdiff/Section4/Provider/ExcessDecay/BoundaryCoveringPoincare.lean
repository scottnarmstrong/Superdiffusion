/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryPoincareWindow
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowNormalized

/-!
# The boundary Poincaré on the covering cube

The boundary energy assembly reads its `L²` object on the **covering cube** `c + □_{n+2}`:

```text
  ‖u - h‖_{L̄²(c+□_{n+2})} ≤ 3^d · C(d) · 3ⁿ · Σᵢ ‖∂ᵢ(u-h)‖_{L̄²(W')} .
```

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Finiteness transports to the volume-normalized measure. -/
theorem eLpNorm_normalizedVolumeMeasureOn_ne_top {A : Set (Vec d)}
    {f : Vec d → ℝ} (hf : eLpNorm f 2 (volume.restrict A) ≠ ⊤) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn A) ≠ ⊤ := by
  rw [eLpNorm_normalizedVolumeMeasureOn_eq]
  by_cases h0 : volume A = 0
  · have hzero : volume.restrict A = 0 := Measure.restrict_eq_zero.2 h0
    rw [hzero, eLpNorm_measure_zero, mul_zero]
    exact ENNReal.zero_ne_top
  · refine ENNReal.mul_ne_top ?_ hf
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.inv_ne_top.2 h0)

/-- **The boundary Poincaré on the covering cube.** -/
theorem eLpNorm_coveringCube_sub_le_boundaryWindowPoincare {n m : ℤ}
    {x z : Vec d} (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hfr : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      frontier (openCubeSet (originCube d m))) ≠ ∅)
    (u h : H1Function (openCubeSet (originCube d m)))
    (w : H10Function (openCubeSet (originCube d m)))
    (hval : ∀ y, w.toFun y = u.toFun y - h.toFun y)
    (hgrad : ∀ y, w.grad y = u.grad y - h.grad y) :
    (eLpNorm (fun y => u.toFun y - h.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => wellPlacedCentre x m (n + 2) + y) ''
            openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d * (boundaryWindowPoincareConst d * (3 : ℝ) ^ n) *
        ∑ i : Fin d,
          (eLpNorm (fun y => u.grad y i - h.grad y i) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by
  classical
  -- finiteness of the window norm
  have hsub : (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) ⊆ openCubeSet (originCube d m) :=
    Set.inter_subset_right
  have hmemWin : MemLp (fun y => u.toFun y - h.toFun y) 2
      (volume.restrict ((((fun y' => z + y') ''
        openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))) :=
    (u.memL2.sub h.memL2).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hfinWin : eLpNorm (fun y => u.toFun y - h.toFun y) 2
      (Support.normalizedVolumeMeasureOn ((((fun y' => z + y') ''
        openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))) ≠ ⊤ :=
    eLpNorm_normalizedVolumeMeasureOn_ne_top hmemWin.2.ne
  -- the covering transport, in real form
  have htrans := eLpNorm_coveringCube_le_anchorWindow hnm hx hgeom
    (fun y => u.toFun y - h.toFun y)
  have hRne : ENNReal.ofReal ((3 : ℝ) ^ d) *
      eLpNorm (fun y => u.toFun y - h.toFun y) 2
        (Support.normalizedVolumeMeasureOn ((((fun y' => z + y') ''
          openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinWin
  have hreal := ENNReal.toReal_mono hRne htrans
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  -- the boundary Poincaré on the window
  have hpoin := eLpNorm_sub_le_boundaryWindowPoincare hfr u h w hval hgrad
  have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  calc (eLpNorm (fun y => u.toFun y - h.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => wellPlacedCentre x m (n + 2) + y) ''
            openCubeSet (originCube d (n + 2))))).toReal
      ≤ (3 : ℝ) ^ d *
          (eLpNorm (fun y => u.toFun y - h.toFun y) 2
            (Support.normalizedVolumeMeasureOn ((((fun y' => z + y') ''
              openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := hreal
    _ ≤ (3 : ℝ) ^ d *
          (boundaryWindowPoincareConst d * (3 : ℝ) ^ n *
            ∑ i : Fin d,
              (eLpNorm (fun y => u.grad y i - h.grad y i) 2
                (Support.normalizedVolumeMeasureOn ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal) :=
        mul_le_mul_of_nonneg_left hpoin h3d
    _ = (3 : ℝ) ^ d * (boundaryWindowPoincareConst d * (3 : ℝ) ^ n) *
          ∑ i : Fin d,
            (eLpNorm (fun y => u.grad y i - h.grad y i) 2
              (Support.normalizedVolumeMeasureOn ((((fun y' => z + y') ''
                openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
