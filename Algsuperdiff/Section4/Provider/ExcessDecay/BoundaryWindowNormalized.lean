/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowPoincare
import Algsuperdiff.Section4.Support.Dirichlet

/-!
# The boundary Poincaré inequality in the anchor's carriers

`BoundaryWindowPoincare` proves the boundary Poincaré inequality against
CoarseGraining's own domain measure `volume.restrict W'`.  The frozen
statement prices every window norm against the **volume-normalized** measure
`Support.normalizedVolumeMeasureOn W'`.  Since the estimate is homogeneous —
the *same* window on both sides — the normalization cancels exactly and the
constant is unchanged.  That is the content of
`eLpNorm_normalized_le_boundaryWindowPoincare`.

`eLpNorm_coordSum_le_dim_mul` then converts the coordinate sum on the right into
the anchor's vector `eLpNorm` of the gradient, at the factor `d` (the ambient
`Vec d = Fin d → ℝ` carries the sup norm, so each coordinate is dominated by the
vector pointwise; the factor is the number of coordinates, not `√d`).

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The volume-normalized `L²` norm is the restricted one times a scalar that
does not depend on the function. -/
theorem eLpNorm_normalizedVolumeMeasureOn_eq (A : Set (Vec d)) (f : Vec d → ℝ) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn A) =
      ((volume A)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm f 2 (volume.restrict A) := by
  rw [Support.normalizedVolumeMeasureOn_def,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num

/-- **The boundary Poincaré inequality, volume-normalized.**

The frozen carrier: the same estimate as
`eLpNorm_le_boundaryWindowPoincare`, at the same constant, against the
volume-normalized measure of the anchor's own window. -/
theorem eLpNorm_normalized_le_boundaryWindowPoincare {n m : ℤ} {z : Vec d}
    (hfr : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      frontier (openCubeSet (originCube d m))) ≠ ∅)
    (u : H10Function (openCubeSet (originCube d m))) :
    (eLpNorm u.toFun 2 (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal ≤
      boundaryWindowPoincareConst d * (3 : ℝ) ^ n *
        ∑ i : Fin d,
          (eLpNorm (fun x => u.grad x i) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by
  classical
  have hbase := eLpNorm_le_boundaryWindowPoincare hfr u
  simp only [eLpNorm_normalizedVolumeMeasureOn_eq, ENNReal.toReal_mul]
  have hr : (0 : ℝ) ≤ (((volume ((((fun y' => z + y') ''
      openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))))⁻¹) ^ (1 / 2 : ℝ)).toReal :=
    ENNReal.toReal_nonneg
  calc (((volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))⁻¹) ^ (1 / 2 : ℝ)).toReal *
        (eLpNorm u.toFun 2 (volume.restrict
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))).toReal
      ≤ (((volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))⁻¹) ^ (1 / 2 : ℝ)).toReal *
          (boundaryWindowPoincareConst d * (3 : ℝ) ^ n *
            ∑ i : Fin d,
              (eLpNorm (fun x => u.grad x i) 2 (volume.restrict
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal) :=
        mul_le_mul_of_nonneg_left hbase hr
    _ = boundaryWindowPoincareConst d * (3 : ℝ) ^ n *
          ∑ i : Fin d,
            (((volume ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))⁻¹) ^ (1 / 2 : ℝ)).toReal *
              (eLpNorm (fun x => u.grad x i) 2 (volume.restrict
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal := by
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring

/-- **The boundary Poincaré on the Dirichlet difference.**

The shape the boundary energy assembly consumes: the zero-trace datum is
presented, exactly as in the frozen statement's own binders, by a witness
`w ∈ H¹₀(□_m)` together with the two pointwise identifications of its value and
its gradient with `u - h`. -/
theorem eLpNorm_sub_le_boundaryWindowPoincare {n m : ℤ} {z : Vec d}
    (hfr : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      frontier (openCubeSet (originCube d m))) ≠ ∅)
    (u h : H1Function (openCubeSet (originCube d m)))
    (w : H10Function (openCubeSet (originCube d m)))
    (hval : ∀ y, w.toFun y = u.toFun y - h.toFun y)
    (hgrad : ∀ y, w.grad y = u.grad y - h.grad y) :
    (eLpNorm (fun y => u.toFun y - h.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))))).toReal ≤
      boundaryWindowPoincareConst d * (3 : ℝ) ^ n *
        ∑ i : Fin d,
          (eLpNorm (fun x => u.grad x i - h.grad x i) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal := by
  have hbase := eLpNorm_normalized_le_boundaryWindowPoincare hfr w
  have hf : (fun y => u.toFun y - h.toFun y) = w.toFun := by
    funext y
    exact (hval y).symm
  have hg : ∀ i : Fin d,
      (fun x => u.grad x i - h.grad x i) = fun x => w.grad x i := by
    intro i
    funext x
    rw [hgrad x]
    rfl
  rw [hf]
  simp only [hg]
  exact hbase

/-- The coordinate sum of gradient `L²` norms is at most `d` times the vector
`L²` norm.  (`Vec d` carries the sup norm, so each coordinate is dominated
pointwise; the factor is the number of coordinates.) -/
theorem eLpNorm_coordSum_le_dim_mul {mu : Measure (Vec d)} (G : Vec d → Vec d)
    (hfin : eLpNorm G 2 mu ≠ ⊤) :
    ∑ i : Fin d, (eLpNorm (fun x => G x i) 2 mu).toReal ≤
      (d : ℝ) * (eLpNorm G 2 mu).toReal := by
  classical
  have hterm : ∀ i : Fin d, (eLpNorm (fun x => G x i) 2 mu).toReal ≤
      (eLpNorm G 2 mu).toReal := by
    intro i
    refine ENNReal.toReal_mono hfin ?_
    exact eLpNorm_mono fun x => norm_le_pi_norm (G x) i
  calc ∑ i : Fin d, (eLpNorm (fun x => G x i) 2 mu).toReal
      ≤ ∑ _i : Fin d, (eLpNorm G 2 mu).toReal :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * (eLpNorm G 2 mu).toReal := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
