import Algsuperdiff.Frozen.Section24.MatrixSecondDerivativeNorm
import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import Homogenization.Sobolev.WeakDerivatives

/-!
# Entry bounds for the frozen derivative norms

`Algsuperdiff.Frozen.Section24.matrixDerivativeNorm` and
`Algsuperdiff.Frozen.Section24.matrixSecondDerivativeNorm` are suprema of
Euclidean matrix norms over the `vecNorm`-unit ball.  Two facts about them are
needed to feed the `W^{1,∞}`-to-Lipschitz bridge from the frozen
`UnitCubeSkewW2Infinity` carrier:

* every coordinate entry of a derivative evaluated at a basis direction is
  dominated by the derivative norm (`abs_entry_apply_le_matrixDerivativeNorm`,
  `abs_entry_apply_apply_le_matrixSecondDerivativeNorm`), and
* the derivative norm is itself dominated by a fixed multiple of the sum of the
  absolute values of those entries (`matrixDerivativeNorm_le_sq_mul_sum`,
  `matrixSecondDerivativeNorm_le_sq_mul_sum`).

The second family is what turns the entrywise `L^∞` memberships stored in the
frozen carrier into finiteness of the `L^∞` norms appearing in
`UnitCubeSkewW2Infinity.w1Infinity` and
`UnitCubeSkewW2Infinity.gradientW1Infinity`, without which those real numbers
carry no information.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz

open Homogenization Homogenization.Book.Ch02 Algsuperdiff.Frozen.Section24
open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ}

/-! ## Elementary comparisons between the ambient and Euclidean norms -/

/-- The ambient supremum norm on `Vec d` is bounded by the Euclidean norm. -/
theorem norm_vec_le_vecNorm (v : Vec d) : ‖v‖ ≤ vecNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vecNorm_nonneg v)]
  intro i
  simpa [vecNorm] using
    (PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) i)

theorem vecNorm_basisVec_le_one (k : Fin d) : vecNorm (basisVec k) ≤ 1 := by
  have hsq : vecNorm (basisVec k) ^ 2 = 1 := by
    rw [vecNorm_sq_eq_vecNormSq, vecNormSq_basisVec]
  nlinarith [vecNorm_nonneg (basisVec k), hsq]

theorem vecNorm_zero_le_one : vecNorm (0 : Vec d) ≤ 1 := by
  have : vecNorm (0 : Vec d) = 0 := by simp [vecNorm]
  rw [this]
  norm_num

/-! ## Entrywise comparisons for matrices -/

theorem norm_mat_le_sum_abs_entries (A : Mat d) :
    ‖A‖ ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| := by
  have hnn : (0 : ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| := by positivity
  rw [Matrix.norm_le_iff hnn]
  intro i j
  rw [Real.norm_eq_abs]
  calc |A i j|
      ≤ ∑ j' : Fin d, |A i j'| :=
        Finset.single_le_sum (f := fun j' => |A i j'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin d, ∑ j' : Fin d, |A i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin d, |A i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem sum_abs_entries_le_sq_mul_norm (A : Mat d) :
    (∑ i : Fin d, ∑ j : Fin d, |A i j|) ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  calc (∑ i : Fin d, ∑ j : Fin d, |A i j|)
      ≤ ∑ _i : Fin d, ∑ _j : Fin d, ‖A‖ := by
        gcongr with i _ j _
        simpa [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm A
    _ = (d : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem matrixNorm_le_sq_mul_norm (A : Mat d) :
    matrixNorm A ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  rw [matrixNorm_eq_matrixOperatorNorm]
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    ((matrixFrobeniusNorm_le_sum_abs_entries A).trans (sum_abs_entries_le_sq_mul_norm A))

/-! ## Operator norms through the coordinate directions -/

/-- Vector-valued form of `Homogenization.norm_clm_le_sum_basisVec_apply`. -/
theorem norm_le_sum_basisVec_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Vec d →L[ℝ] F) : ‖L‖ ≤ ∑ k : Fin d, ‖L (basisVec k)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_
  intro x
  have hx : L x = ∑ k : Fin d, x k • L (basisVec k) := by
    calc L x = ∑ k : Fin d, x k • L (fun j => if k = j then 1 else 0) := by
          simpa using (LinearMap.pi_apply_eq_sum_univ (f := L.toLinearMap) x)
      _ = ∑ k : Fin d, x k • L (basisVec k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hfun : (fun j => if k = j then 1 else 0) = basisVec k := by
            funext j
            simp [basisVec_apply, eq_comm]
          rw [hfun]
  rw [hx]
  calc ‖∑ k : Fin d, x k • L (basisVec k)‖
      ≤ ∑ k : Fin d, ‖x k • L (basisVec k)‖ := norm_sum_le _ _
    _ = ∑ k : Fin d, ‖x k‖ * ‖L (basisVec k)‖ := by
        simp [norm_smul]
    _ ≤ ∑ k : Fin d, ‖x‖ * ‖L (basisVec k)‖ := by
        gcongr with k _
        exact norm_le_pi_norm x k
    _ = (∑ k : Fin d, ‖L (basisVec k)‖) * ‖x‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-! ## The frozen first-derivative norm -/

theorem matrixDerivativeNorm_range_bddAbove (D : Vec d →L[ℝ] Mat d) :
    BddAbove (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} => matrixNorm (D v.1)) := by
  refine ⟨(d : ℝ) ^ 2 * ‖D‖, ?_⟩
  rintro c ⟨v, rfl⟩
  calc matrixNorm (D v.1) ≤ (d : ℝ) ^ 2 * ‖D v.1‖ := matrixNorm_le_sq_mul_norm _
    _ ≤ (d : ℝ) ^ 2 * (‖D‖ * ‖v.1‖) := by
        gcongr
        exact D.le_opNorm _
    _ ≤ (d : ℝ) ^ 2 * (‖D‖ * 1) := by
        gcongr
        exact (norm_vec_le_vecNorm v.1).trans v.2
    _ = (d : ℝ) ^ 2 * ‖D‖ := by ring

theorem matrixDerivativeNorm_range_nonempty (D : Vec d →L[ℝ] Mat d) :
    (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} => matrixNorm (D v.1)).Nonempty :=
  ⟨matrixNorm (D 0), ⟨⟨0, vecNorm_zero_le_one⟩, rfl⟩⟩

/-- The frozen first-derivative norm dominates every Euclidean matrix norm on
the Euclidean unit ball. -/
theorem matrixNorm_apply_le_matrixDerivativeNorm (D : Vec d →L[ℝ] Mat d) (v : Vec d)
    (hv : vecNorm v ≤ 1) : matrixNorm (D v) ≤ matrixDerivativeNorm D :=
  le_csSup (matrixDerivativeNorm_range_bddAbove D) ⟨⟨v, hv⟩, rfl⟩

theorem matrixDerivativeNorm_nonneg (D : Vec d →L[ℝ] Mat d) :
    0 ≤ matrixDerivativeNorm D :=
  (matrixNorm_nonneg (D 0)).trans
    (matrixNorm_apply_le_matrixDerivativeNorm D 0 vecNorm_zero_le_one)

/-- Every coordinate entry of a derivative in a coordinate direction is bounded
by the frozen first-derivative norm. -/
theorem abs_entry_apply_le_matrixDerivativeNorm (D : Vec d →L[ℝ] Mat d) (k i j : Fin d) :
    |D (basisVec k) i j| ≤ matrixDerivativeNorm D := by
  refine le_trans ?_
    (matrixNorm_apply_le_matrixDerivativeNorm D (basisVec k) (vecNorm_basisVec_le_one k))
  rw [matrixNorm_eq_matrixOperatorNorm]
  exact abs_entry_le_matrixOperatorNorm _ i j

theorem matrixDerivativeNorm_le_sq_mul_norm (D : Vec d →L[ℝ] Mat d) :
    matrixDerivativeNorm D ≤ (d : ℝ) ^ 2 * ‖D‖ := by
  refine csSup_le (matrixDerivativeNorm_range_nonempty D) ?_
  rintro c ⟨v, rfl⟩
  calc matrixNorm (D v.1) ≤ (d : ℝ) ^ 2 * ‖D v.1‖ := matrixNorm_le_sq_mul_norm _
    _ ≤ (d : ℝ) ^ 2 * (‖D‖ * ‖v.1‖) := by
        gcongr
        exact D.le_opNorm _
    _ ≤ (d : ℝ) ^ 2 * (‖D‖ * 1) := by
        gcongr
        exact (norm_vec_le_vecNorm v.1).trans v.2
    _ = (d : ℝ) ^ 2 * ‖D‖ := by ring

/-- The frozen first-derivative norm is dominated by the coordinate entries. -/
theorem matrixDerivativeNorm_le_sq_mul_sum (D : Vec d →L[ℝ] Mat d) :
    matrixDerivativeNorm D ≤
      (d : ℝ) ^ 2 * ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d, |D (basisVec k) i j| := by
  refine (matrixDerivativeNorm_le_sq_mul_norm D).trans ?_
  have hstep : ‖D‖ ≤ ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d, |D (basisVec k) i j| := by
    refine (norm_le_sum_basisVec_apply D).trans ?_
    gcongr with k _
    exact norm_mat_le_sum_abs_entries _
  gcongr

/-! ## The frozen second-derivative norm -/

theorem matrixSecondDerivativeNorm_range_bddAbove
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :
    BddAbove (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} =>
      matrixDerivativeNorm (H v.1)) := by
  refine ⟨(d : ℝ) ^ 2 * ‖H‖, ?_⟩
  rintro c ⟨v, rfl⟩
  calc matrixDerivativeNorm (H v.1) ≤ (d : ℝ) ^ 2 * ‖H v.1‖ :=
        matrixDerivativeNorm_le_sq_mul_norm _
    _ ≤ (d : ℝ) ^ 2 * (‖H‖ * ‖v.1‖) := by
        gcongr
        exact H.le_opNorm _
    _ ≤ (d : ℝ) ^ 2 * (‖H‖ * 1) := by
        gcongr
        exact (norm_vec_le_vecNorm v.1).trans v.2
    _ = (d : ℝ) ^ 2 * ‖H‖ := by ring

theorem matrixSecondDerivativeNorm_range_nonempty
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :
    (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} =>
      matrixDerivativeNorm (H v.1)).Nonempty :=
  ⟨matrixDerivativeNorm (H 0), ⟨⟨0, vecNorm_zero_le_one⟩, rfl⟩⟩

theorem matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) (v : Vec d) (hv : vecNorm v ≤ 1) :
    matrixDerivativeNorm (H v) ≤ matrixSecondDerivativeNorm H :=
  le_csSup (matrixSecondDerivativeNorm_range_bddAbove H) ⟨⟨v, hv⟩, rfl⟩

theorem matrixSecondDerivativeNorm_nonneg (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :
    0 ≤ matrixSecondDerivativeNorm H :=
  (matrixDerivativeNorm_nonneg (H 0)).trans
    (matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H 0 vecNorm_zero_le_one)

/-- Every coordinate entry of a second derivative in two coordinate directions is
bounded by the frozen second-derivative norm. -/
theorem abs_entry_apply_apply_le_matrixSecondDerivativeNorm
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) (l k i j : Fin d) :
    |H (basisVec l) (basisVec k) i j| ≤ matrixSecondDerivativeNorm H :=
  (abs_entry_apply_le_matrixDerivativeNorm (H (basisVec l)) k i j).trans
    (matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H (basisVec l)
      (vecNorm_basisVec_le_one l))

/-- The frozen second-derivative norm is dominated by the coordinate entries. -/
theorem matrixSecondDerivativeNorm_le_sq_mul_sum (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :
    matrixSecondDerivativeNorm H ≤
      (d : ℝ) ^ 2 * ∑ l : Fin d, ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        |H (basisVec l) (basisVec k) i j| := by
  have hnorm : ‖H‖ ≤ ∑ l : Fin d, ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d,
      |H (basisVec l) (basisVec k) i j| := by
    refine (norm_le_sum_basisVec_apply H).trans ?_
    gcongr with l _
    refine (norm_le_sum_basisVec_apply (H (basisVec l))).trans ?_
    gcongr with k _
    exact norm_mat_le_sum_abs_entries _
  refine csSup_le (matrixSecondDerivativeNorm_range_nonempty H) ?_
  rintro c ⟨v, rfl⟩
  calc matrixDerivativeNorm (H v.1) ≤ (d : ℝ) ^ 2 * ‖H v.1‖ :=
        matrixDerivativeNorm_le_sq_mul_norm _
    _ ≤ (d : ℝ) ^ 2 * (‖H‖ * ‖v.1‖) := by
        gcongr
        exact H.le_opNorm _
    _ ≤ (d : ℝ) ^ 2 * (‖H‖ * 1) := by
        gcongr
        exact (norm_vec_le_vecNorm v.1).trans v.2
    _ = (d : ℝ) ^ 2 * ‖H‖ := by ring
    _ ≤ (d : ℝ) ^ 2 * ∑ l : Fin d, ∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d,
          |H (basisVec l) (basisVec k) i j| := by
        gcongr

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
