import Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.Assembly
import Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.MatrixNorms
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.W1Infinity
import Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.GradientW1Infinity
import Homogenization.Geometry.CubeMeasure

/-!
# Lipschitz representatives at the frozen unit-cube `W^{2,∞}` carrier

The carrier of `Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity` is the
*open* unit triadic cube `cubeDomain (originCube d 0)`, which is a bounded open
convex domain, so the bridge of
`Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.Assembly` applies
directly.  This module discharges its hypotheses from the frozen fields and
records the two consumer corollaries:

* `exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value`: every entry of the
  matrix field has a globally `d * h.w1Infinity`-Lipschitz representative;
* `exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv`: every entry of the
  first-derivative field has a globally `d * h.gradientW1Infinity`-Lipschitz
  representative.

Both are stated pointwise (an oscillation bound valid for every pair of points
and an a.e. identification with the frozen entry function), which is the form
the `D_h`-bound assembly and the Besov estimates consume.

The `L^∞` finiteness that gives `w1Infinity` and `gradientW1Infinity` their
meaning is *derived* here from the entrywise `L^∞` memberships stored in the
frozen structure, via `MatrixNorms`; it is never assumed.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz

open Homogenization Homogenization.Book.Ch02 Algsuperdiff.Frozen.Section24 MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

variable {d : ℕ}

/-! ## `L^∞` bookkeeping -/

/-- An a.e. uniform bound makes the essential supremum finite. -/
theorem eLpNorm_top_ne_top_of_ae_abs_le {μ : Measure (Vec d)} {F : Vec d → ℝ} {C : ℝ}
    (hF : ∀ᵐ x ∂μ, |F x| ≤ C) : eLpNorm F ∞ μ ≠ ⊤ := by
  rw [MeasureTheory.eLpNorm_exponent_top]
  exact (MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound (C := C)
    (by simpa [Real.norm_eq_abs] using hF)).ne

/-- A finite essential supremum is an a.e. pointwise bound. -/
theorem ae_abs_le_toReal_eLpNorm_top {μ : Measure (Vec d)} {F : Vec d → ℝ}
    (hfin : eLpNorm F ∞ μ ≠ ⊤) :
    ∀ᵐ x ∂μ, |F x| ≤ ENNReal.toReal (eLpNorm F ∞ μ) := by
  have hle : ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ eLpNorm F ∞ μ := by
    rw [MeasureTheory.eLpNorm_exponent_top]
    exact MeasureTheory.ae_le_eLpNormEssSup
  filter_upwards [hle] with x hx
  have := ENNReal.toReal_mono hfin hx
  simpa [Real.norm_eq_abs] using this

/-! ## Entrywise a.e. bounds through the frozen derivative norms -/

/-- Every coordinate entry of a derivative field is bounded a.e. by the
essential supremum of the frozen first-derivative norm, whose finiteness follows
from the entrywise `L^∞` memberships. -/
theorem ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm
    {U : Set (Vec d)} {D : Vec d → Vec d →L[ℝ] Mat d}
    (hmem : ∀ k i j : Fin d, MemLp (fun x => D x (basisVec k) i j) ∞ (volumeMeasureOn U))
    (k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn U,
      |D x (basisVec k) i j| ≤
        ENNReal.toReal (eLpNorm (fun y => matrixDerivativeNorm (D y)) ∞ (volumeMeasureOn U)) := by
  classical
  have hall : ∀ᵐ x ∂ volumeMeasureOn U, ∀ k' i' j' : Fin d,
      |D x (basisVec k') i' j'| ≤
        ENNReal.toReal (eLpNorm (fun y => D y (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    rw [MeasureTheory.ae_all_iff]
    intro k'
    rw [MeasureTheory.ae_all_iff]
    intro i'
    rw [MeasureTheory.ae_all_iff]
    intro j'
    exact ae_abs_le_toReal_eLpNorm_top (hmem k' i' j').eLpNorm_lt_top.ne
  have hbd : ∀ᵐ x ∂ volumeMeasureOn U, |matrixDerivativeNorm (D x)| ≤
      (d : ℝ) ^ 2 * ∑ k' : Fin d, ∑ i' : Fin d, ∑ j' : Fin d,
        ENNReal.toReal (eLpNorm (fun y => D y (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    filter_upwards [hall] with x hx
    rw [abs_of_nonneg (matrixDerivativeNorm_nonneg _)]
    refine (matrixDerivativeNorm_le_sq_mul_sum (D x)).trans ?_
    gcongr with k' _ i' _ j' _
    exact hx k' i' j'
  filter_upwards [ae_abs_le_toReal_eLpNorm_top (eLpNorm_top_ne_top_of_ae_abs_le hbd)] with x hx
  exact (abs_entry_apply_le_matrixDerivativeNorm (D x) k i j).trans ((le_abs_self _).trans hx)

/-- Second-derivative analogue of
`ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm`. -/
theorem ae_abs_apply_apply_le_toReal_eLpNorm_matrixSecondDerivativeNorm
    {U : Set (Vec d)} {H : Vec d → Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)}
    (hmem : ∀ l k i j : Fin d,
      MemLp (fun x => H x (basisVec l) (basisVec k) i j) ∞ (volumeMeasureOn U))
    (l k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn U,
      |H x (basisVec l) (basisVec k) i j| ≤
        ENNReal.toReal
          (eLpNorm (fun y => matrixSecondDerivativeNorm (H y)) ∞ (volumeMeasureOn U)) := by
  classical
  have hall : ∀ᵐ x ∂ volumeMeasureOn U, ∀ l' k' i' j' : Fin d,
      |H x (basisVec l') (basisVec k') i' j'| ≤
        ENNReal.toReal
          (eLpNorm (fun y => H y (basisVec l') (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    rw [MeasureTheory.ae_all_iff]
    intro l'
    rw [MeasureTheory.ae_all_iff]
    intro k'
    rw [MeasureTheory.ae_all_iff]
    intro i'
    rw [MeasureTheory.ae_all_iff]
    intro j'
    exact ae_abs_le_toReal_eLpNorm_top (hmem l' k' i' j').eLpNorm_lt_top.ne
  have hbd : ∀ᵐ x ∂ volumeMeasureOn U, |matrixSecondDerivativeNorm (H x)| ≤
      (d : ℝ) ^ 2 * ∑ l' : Fin d, ∑ k' : Fin d, ∑ i' : Fin d, ∑ j' : Fin d,
        ENNReal.toReal
          (eLpNorm (fun y => H y (basisVec l') (basisVec k') i' j') ∞ (volumeMeasureOn U)) := by
    filter_upwards [hall] with x hx
    rw [abs_of_nonneg (matrixSecondDerivativeNorm_nonneg _)]
    refine (matrixSecondDerivativeNorm_le_sq_mul_sum (H x)).trans ?_
    gcongr with l' _ k' _ i' _ j' _
    exact hx l' k' i' j'
  filter_upwards [ae_abs_le_toReal_eLpNorm_top (eLpNorm_top_ne_top_of_ae_abs_le hbd)] with x hx
  exact (abs_entry_apply_apply_le_matrixSecondDerivativeNorm (H x) l k i j).trans
    ((le_abs_self _).trans hx)

/-! ## The frozen unit-cube norms -/

theorem w1Infinity_nonneg (h : UnitCubeSkewW2Infinity d) : 0 ≤ h.w1Infinity := by
  simp only [UnitCubeSkewW2Infinity.w1Infinity]
  exact le_trans ENNReal.toReal_nonneg (le_max_left _ _)

theorem gradientW1Infinity_nonneg (h : UnitCubeSkewW2Infinity d) :
    0 ≤ h.gradientW1Infinity := by
  simp only [UnitCubeSkewW2Infinity.gradientW1Infinity]
  exact le_trans ENNReal.toReal_nonneg (le_max_left _ _)

theorem toReal_eLpNorm_matrixDerivativeNorm_le_w1Infinity (h : UnitCubeSkewW2Infinity d) :
    ENNReal.toReal (eLpNorm (fun x => matrixDerivativeNorm (h.firstDeriv x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) ≤
      h.w1Infinity := by
  simp only [UnitCubeSkewW2Infinity.w1Infinity]
  exact le_max_left _ _

theorem toReal_eLpNorm_matrixSecondDerivativeNorm_le_gradientW1Infinity
    (h : UnitCubeSkewW2Infinity d) :
    ENNReal.toReal (eLpNorm (fun x => matrixSecondDerivativeNorm (h.secondDeriv x)) ∞
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) ≤
      h.gradientW1Infinity := by
  simp only [UnitCubeSkewW2Infinity.gradientW1Infinity]
  exact le_max_left _ _

/-! ## Entrywise a.e. derivative bounds at the frozen carrier -/

theorem ae_abs_firstDeriv_le_w1Infinity (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      |h.firstDeriv x (basisVec k) i j| ≤ h.w1Infinity := by
  filter_upwards [ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm
    (D := h.firstDeriv) (fun k' i' j' => h.firstDeriv_memLp k' i' j') k i j] with x hx
  exact hx.trans (toReal_eLpNorm_matrixDerivativeNorm_le_w1Infinity h)

theorem ae_abs_secondDeriv_le_gradientW1Infinity (h : UnitCubeSkewW2Infinity d)
    (l k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      |h.secondDeriv x (basisVec l) (basisVec k) i j| ≤ h.gradientW1Infinity := by
  filter_upwards [ae_abs_apply_apply_le_toReal_eLpNorm_matrixSecondDerivativeNorm
    (H := h.secondDeriv) (fun l' k' i' j' => h.secondDeriv_memLp l' k' i' j') l k i j] with x hx
  exact hx.trans (toReal_eLpNorm_matrixSecondDerivativeNorm_le_gradientW1Infinity h)

/-! ## The consumer corollaries -/

/-- **Lipschitz representative of a frozen unit-cube matrix-field entry.** -/
theorem exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value
    (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.w1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
          fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j :=
  exists_lipschitz_ae_eq_of_hasWeakPartialDeriv_bound
    (U := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u := fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j)
    (g := fun k x => h.firstDeriv x (basisVec k) i j)
    (B := h.w1Infinity)
    (cubeDomain (originCube d 0)).isDomain
    (w1Infinity_nonneg h)
    (h.toLInfSkewMatrixFieldOn.1.2 i j)
    (fun k => h.firstDeriv_memLp k i j)
    (fun k => ae_abs_firstDeriv_le_w1Infinity h k i j)
    (fun k => h.hasWeakPartialDeriv_value k i j)

/-- **Lipschitz representative of a frozen unit-cube first-derivative entry.** -/
theorem exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv
    (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.gradientW1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
          fun x => h.firstDeriv x (basisVec k) i j :=
  exists_lipschitz_ae_eq_of_hasWeakPartialDeriv_bound
    (U := ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (u := fun x => h.firstDeriv x (basisVec k) i j)
    (g := fun l x => h.secondDeriv x (basisVec l) (basisVec k) i j)
    (B := h.gradientW1Infinity)
    (cubeDomain (originCube d 0)).isDomain
    (gradientW1Infinity_nonneg h)
    (h.firstDeriv_memLp k i j)
    (fun l => h.secondDeriv_memLp l k i j)
    (fun l => ae_abs_secondDeriv_le_gradientW1Infinity h l k i j)
    (fun l => h.hasWeakPartialDeriv_firstDeriv l k i j)

/-! ## Half-open cube form

The frozen carrier lives on the *open* unit cube, while the Besov and cube
average machinery integrates over the half-open realization `cubeSet`.  The two
restricted measures coincide, so the a.e. identifications transfer verbatim. -/

/-- Half-open-cell form of
`exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value`. -/
theorem exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_value
    (h : UnitCubeSkewW2Infinity d) (i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.w1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn (cubeSet (originCube d 0))]
          fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j := by
  obtain ⟨v, hlip, heq⟩ := exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_value h i j
  refine ⟨v, hlip, ?_⟩
  rwa [volumeMeasureOn, Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- Half-open-cell form of
`exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv`. -/
theorem exists_lipschitz_ae_eq_cubeSet_unitCubeSkewW2Infinity_firstDeriv
    (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    ∃ v : Vec d → ℝ,
      (∀ x y : Vec d, ‖v x - v y‖ ≤ (d : ℝ) * h.gradientW1Infinity * ‖x - y‖) ∧
        v =ᵐ[volumeMeasureOn (cubeSet (originCube d 0))]
          fun x => h.firstDeriv x (basisVec k) i j := by
  obtain ⟨v, hlip, heq⟩ := exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv h k i j
  refine ⟨v, hlip, ?_⟩
  rwa [volumeMeasureOn, Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
