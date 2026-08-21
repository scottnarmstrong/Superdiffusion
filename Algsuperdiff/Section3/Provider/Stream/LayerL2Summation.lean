import Algsuperdiff.Section3.Provider.Stream.LayerL2Algebra
import Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality

/-!
# Uniform two-gap summation for the finite-shell Frobenius mass

This internal module sums the corrected one-shell diagonal and ordered-pair
scales.  The finer-shell spatial gain makes both integer gaps geometric, so no
factor depending on `M.gamma` is lost.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- A finite integer tail of `3^(-alpha r)` is bounded by the full series. -/
theorem sum_Ioc_rpow_decay_le_inv_geometricDiscount {alpha : ℝ}
    (halpha : 0 < alpha) (n m : ℤ) :
    (∑ k ∈ Finset.Ioc n m,
      (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ))) ≤
        (Homogenization.geometricDiscount alpha 1)⁻¹ := by
  classical
  let f : ℕ → ℝ := fun r => (3 : ℝ) ^ (-alpha * (r : ℝ))
  let s : Finset ℕ := (Finset.Ioc n m).image fun k => (m - k).toNat
  have hinj : Set.InjOn (fun k : ℤ => (m - k).toNat) (Finset.Ioc n m) := by
    intro a ha b hb hab
    have ha' : a ≤ m := (Finset.mem_Ioc.mp ha).2
    have hb' : b ≤ m := (Finset.mem_Ioc.mp hb).2
    have haeq : ((m - a).toNat : ℤ) = m - a := Int.toNat_of_nonneg (by omega)
    have hbeq : ((m - b).toNat : ℤ) = m - b := Int.toNat_of_nonneg (by omega)
    have hab' : m - a = m - b := by
      rw [← haeq, ← hbeq]
      exact_mod_cast hab
    omega
  have hsumImage :
      (∑ k ∈ Finset.Ioc n m,
        (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ))) =
        ∑ r ∈ s, f r := by
    calc
      (∑ k ∈ Finset.Ioc n m,
          (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ))) =
          ∑ k ∈ Finset.Ioc n m, f (m - k).toNat := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [f]
        have hcast : (((m - k).toNat : ℕ) : ℝ) = ((m - k : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by
            have := (Finset.mem_Ioc.mp hk).2
            omega)
        rw [hcast]
      _ = ∑ r ∈ s, f r := by
        simpa [s] using (Finset.sum_image (s := Finset.Ioc n m)
          (g := fun k : ℤ => (m - k).toNat) (f := f) hinj).symm
  have hsummable : Summable f :=
    Homogenization.Book.Ch05.Section52.summable_rpow_three_neg_mul_nat halpha
  rw [hsumImage]
  calc
    (∑ r ∈ s, f r) ≤ ∑' r : ℕ, f r :=
      hsummable.sum_le_tsum s (fun r _ => Real.rpow_nonneg (by norm_num) _)
    _ = (Homogenization.geometricDiscount alpha 1)⁻¹ := by
      simpa [f] using
        Homogenization.Book.Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount
          halpha

/-- The ordered pair window has a uniformly summable two-gap decay. -/
theorem sum_layerOrderedPairs_twoGap_decay_le {alpha : ℝ}
    (halpha : 0 < alpha) (n m : ℤ) :
    (∑ p ∈ layerOrderedPairs n m,
      (3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
        (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ))) ≤
      (Homogenization.geometricDiscount alpha 1)⁻¹ ^ 2 := by
  classical
  let q : ℝ := (Homogenization.geometricDiscount alpha 1)⁻¹
  have hq : 0 ≤ q := by
    dsimp [q]
    exact inv_nonneg.mpr (Homogenization.geometricDiscount_nonneg
      (by simpa using halpha.le))
  have hinner : ∀ k ∈ Finset.Ioc n m,
      (∑ k' ∈ Finset.Ioc n (k - 1),
        (3 : ℝ) ^ (-alpha * ((k - k' : ℤ) : ℝ))) ≤ q := by
    intro k _
    calc
      (∑ k' ∈ Finset.Ioc n (k - 1),
          (3 : ℝ) ^ (-alpha * ((k - k' : ℤ) : ℝ))) ≤
          ∑ k' ∈ Finset.Ioc n k,
            (3 : ℝ) ^ (-alpha * ((k - k' : ℤ) : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k' hk'
          rw [Finset.mem_Ioc] at hk' ⊢
          omega
        · intro k' _ _
          exact Real.rpow_nonneg (by norm_num) _
      _ ≤ q := by
        simpa only [q] using
          sum_Ioc_rpow_decay_le_inv_geometricDiscount halpha n k
  have houter : (∑ k ∈ Finset.Ioc n m,
      (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ))) ≤ q := by
    simpa only [q] using sum_Ioc_rpow_decay_le_inv_geometricDiscount halpha n m
  rw [sum_layerOrderedPairs_eq_nested n m (fun k k' =>
    (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) *
      (3 : ℝ) ^ (-alpha * ((k - k' : ℤ) : ℝ)))]
  calc
    (∑ k ∈ Finset.Ioc n m,
        ∑ k' ∈ Finset.Ioc n (k - 1),
          (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) *
            (3 : ℝ) ^ (-alpha * ((k - k' : ℤ) : ℝ))) =
        ∑ k ∈ Finset.Ioc n m,
          (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) *
            ∑ k' ∈ Finset.Ioc n (k - 1),
              (3 : ℝ) ^ (-alpha * ((k - k' : ℤ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Ioc n m,
        (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) * q := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hinner k hk)
        (Real.rpow_nonneg (by norm_num) _)
    _ = q * ∑ k ∈ Finset.Ioc n m,
        (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ q * q := mul_le_mul_of_nonneg_left houter hq
    _ = (Homogenization.geometricDiscount alpha 1)⁻¹ ^ 2 := by
      dsimp [q]
      ring

/-- Exact exponent factorization for one diagonal shell scale. -/
theorem layerDiagonalScale_factor_eq (M : ABKModel d) (l m k : ℤ) :
    (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) =
      ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) *
        (3 : ℝ) ^ (-(2 * M.gamma + (d : ℝ) / 2) *
          ((m : ℝ) - (k : ℝ))) := by
  repeat' rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- Exact two-gap factorization for an ordered pair scale. -/
theorem layerPairScale_factor_eq (M : ABKModel d) (l m k k' : ℤ) :
    (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) =
      ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) *
        (3 : ℝ) ^ (-(2 * M.gamma + (d : ℝ) / 2) *
          ((m : ℝ) - (k : ℝ))) *
        (3 : ℝ) ^ (-(M.gamma + (d : ℝ) / 2) *
          ((k : ℝ) - (k' : ℝ))) := by
  repeat' rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- Dimension-only amplitude after summing the diagonal shell scales. -/
def layerL2DiagonalSumConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 1 * layerDiagonalAllGapConst d *
    (Homogenization.geometricDiscount ((d : ℝ) / 2) 1)⁻¹

/-- Dimension-only amplitude after summing the ordered-pair scales. -/
def layerL2PairSumConst (d : ℕ) : ℝ :=
  2 * IndependentSums.gammaTriangleConst 1 * layerPairAllGapConst d *
    (Homogenization.geometricDiscount ((d : ℝ) / 2) 1)⁻¹ ^ 2

theorem layerL2DiagonalSumConst_pos (d : ℕ) (hd : 0 < d) :
    0 < layerL2DiagonalSumConst d := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold layerL2DiagonalSumConst
  exact mul_pos
    (mul_pos IndependentSums.gammaTriangleConst_pos
      (layerDiagonalAllGapConst_pos d))
    (inv_pos.mpr (Homogenization.geometricDiscount_pos (by positivity)))

theorem layerL2PairSumConst_pos (d : ℕ) (hd : 0 < d) :
    0 < layerL2PairSumConst d := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold layerL2PairSumConst
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num) IndependentSums.gammaTriangleConst_pos)
      (layerPairAllGapConst_pos d hd))
    (sq_pos_of_pos (inv_pos.mpr
      (Homogenization.geometricDiscount_pos (by positivity))))

end

end Algsuperdiff.Section3.Provider.Stream
