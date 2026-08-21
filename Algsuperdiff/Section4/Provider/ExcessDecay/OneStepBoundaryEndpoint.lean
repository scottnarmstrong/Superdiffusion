/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryDatum
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepConditional

/-!
# The boundary-branch excess-decay endpoint

`OneStepSchauderChain.excessDecay_oneStep_interior_of_harmonicApprox` closed the
four Schauder slots of
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` on the interior
branch, at `K_h = 0`.  This module does the same on the **boundary** branch,
through `OneStepBoundaryDatum.exists_gradientHolder_boundary_split`:

```text
  Csch = boundarySchauderConst d = 48 · 3^{3/2} · schauderConst d · √((24(d+1))^d) ,
  K_h  = boundarySchauderConst d · (3^{-n})^{1/2} · (3^{-(n-2)} · boundaryDatumLeg …) .
```

The competitor enters through **classical harmonicity on the doubled window**
`reflectedWindow x m (n-2)` — which is what
`OneStepSchauderComposeBoundary.exists_classicalCompetitor_reflectedWindow`
produces from a variationally harmonic odd extension — together with its
square-integrability there.  Nothing here restricts the met set: the geometry
of `OneStepBoundaryGeometry` is uniform in it.

## What is still open, precisely

1. **The `_of_weaklyHarmonic` level.**
   `OneStepSchauderComposeInterior.excessDecay_oneStep_interior_of_weaklyHarmonic`
   removes the classical-harmonicity slot by applying Weyl's lemma on the
   anchor's *moved replacement cube* `y + □_{n-2}`, which is exactly where the
   anchor's `hharm` lives.  On the boundary branch the Schauder competitor lives
   on `reflectedWindow x m (n-2)`, and the moved replacement cube is **not**
   contained in it (in a met coordinate the clamped cube protrudes on the window
   side: `windowLo ≥ y_i − ½·3^{n-2}`), so the two representatives must be
   identified on `U_2` — where both are continuous and both agree a.e. with the
   competitor — before `hharm` can be transported.  That identification, plus the
   `EqOn` transfer of `gradField` and of `affineExcess`, is the remaining
   assembly; it is bookkeeping, not analysis.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Square integrability against affine competitors on the doubled window -/

theorem integrableOn_sub_affineEval_sq_reflectedWindow {m k : ℤ} (x : Vec d)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (reflectedWindow x m k)))
    (c : ℝ) (g : Vec d) :
    IntegrableOn (fun p => (u p - affineEval c g p) ^ 2) (reflectedWindow x m k) := by
  refine integrableOn_sub_affineEval_sq_of_axisCubeSandwich
    (zout := fun _ => -(1 / 2) * (3 : ℝ) ^ (m + 2)) (Lout := (3 : ℝ) ^ (m + 2))
    (zpow_pos (by norm_num) (m + 2)) (measurableSet_reflectedWindow x m k) ?_ hu c g
  refine subset_trans (reflectedWindow_subset_openCubeSet x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube]

/-! ## 2. The endpoint -/

/-- **The one-step excess-decay contraction on the boundary branch, with the
gradient-Hölder Schauder estimate discharged.**

Identical to `OneStepConditional.excessDecay_oneStep_of_harmonicApprox` except
that the four Schauder slots are replaced by classical harmonicity of
the competitor on the **doubled** window `reflectedWindow x m (n-2)` (plus its
`L²` data there and the affine minimizer datum on `U_2`); the constant is
`Csch = boundarySchauderConst d` and the boundary-datum leg is the explicit

```text
  K_h = boundarySchauderConst d · (3^{-n})^{1/2} · (3^{-(n-2)} · boundaryDatumLeg x m n v c g) ,
```

which is `0` whenever no face of `∂□_m` is met (`boundaryDatumLeg_of_unmet`), so
that this statement contains the interior display as its unmet case. -/
theorem excessDecay_oneStep_boundary_of_harmonicApprox [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {k : ℕ} (hk : 3 ≤ k) {M : ABKModel d} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {delta : ℝ}
    (hdelta1 : delta ≤ 1) {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m) (hmn : n - 2 < m)
    {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (hvR : MemLp v 2 (volume.restrict (reflectedWindow x m (n - 2))))
    (huv : MemLp (fun y => u y - v y) 2 (volume.restrict (movedReplacementCube x m n)))
    (hharmclass : HarmonicOnNhd (v ∘ Schauder.toEuc.symm)
      ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    {c : ℝ} {g : Vec d} (hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) v c g)
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
      ≤ taylorContractionConst d * boundarySchauderConst d * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d (boundarySchauderConst d) k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
            * (boundarySchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * boundaryDatumLeg x m n v c g)) := by
  have hintsq : ∀ (c' : ℝ) (g' : Vec d),
      IntegrableOn (fun y => (v y - affineEval c' g' y) ^ 2)
        (reflectedWindow x m (n - 2)) volume :=
    fun c' g' => integrableOn_sub_affineEval_sq_reflectedWindow x hvR c' g'
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    Schauder.exists_gradientHolder_boundary_split hd hx hmn hharmclass hintsq hmin
  exact excessDecay_oneStep_of_harmonicApprox hd hk hs hs1 hdelta1 hx hnm hu hv huv hmem hB
    hharm hK (Schauder.boundarySchauderConst_nonneg d) hint hgrad hhol hschauder

end

end Algsuperdiff.Section4.Provider.ExcessDecay
