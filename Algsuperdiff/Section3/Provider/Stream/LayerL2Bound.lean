import Algsuperdiff.Section3.Provider.Stream.LayerL2Summation

/-!
# Corrected all-gap finite-shell Frobenius bound

This module combines the strict diagonal and ordered-pair estimates on their
literal model observables.  The result is the corrected all-gap centered cube
Frobenius estimate needed internally for ABK26 `e.km.kn.L2.bound`; no source
node or frozen-surface status is assigned here.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Final dimension-only amplitude for the centered finite-shell mass. -/
def layerL2AllGapConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 1 *
    (layerL2DiagonalSumConst d + layerL2PairSumConst d)

private theorem diagonalAmplitude_le (M : ABKModel d) (n m l : ℤ) :
    IndependentSums.gammaTriangleConst 1 *
        ∑ k ∈ Finset.Ioc n m,
          layerDiagonalAllGapConst d *
            (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) ≤
      layerL2DiagonalSumConst d *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := by
  let alpha : ℝ := (d : ℝ) / 2
  let base : ℝ :=
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hbase : 0 ≤ base := by dsimp [base]; positivity
  have hC : 0 ≤ layerDiagonalAllGapConst d :=
    (layerDiagonalAllGapConst_pos d).le
  have hterm : ∀ k ∈ Finset.Ioc n m,
      layerDiagonalAllGapConst d *
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) ≤
        layerDiagonalAllGapConst d * base *
          (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) := by
    intro k hk
    have hkm : k ≤ m := (Finset.mem_Ioc.mp hk).2
    have hgap0 : 0 ≤ (m : ℝ) - (k : ℝ) := by exact_mod_cast sub_nonneg.mpr hkm
    have hgap :
        (3 : ℝ) ^ (-(2 * M.gamma + (d : ℝ) / 2) *
            ((m : ℝ) - (k : ℝ))) ≤
          (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [alpha]
      push_cast
      nlinarith [M.shellPrefix.gamma_pos]
    have hfactor := layerDiagonalScale_factor_eq M l m k
    calc
      layerDiagonalAllGapConst d *
            (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) =
          layerDiagonalAllGapConst d *
            ((3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ)))) := by
        ring
      _ = layerDiagonalAllGapConst d *
            (base * (3 : ℝ) ^ (-(2 * M.gamma + (d : ℝ) / 2) *
              ((m : ℝ) - (k : ℝ)))) := by rw [hfactor]
      _ ≤ layerDiagonalAllGapConst d *
          (base * (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgap hbase) hC
      _ = layerDiagonalAllGapConst d * base *
          (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) := by ring
  have hsum := Finset.sum_le_sum hterm
  have hdecay := sum_Ioc_rpow_decay_le_inv_geometricDiscount halpha n m
  have hpre : 0 ≤ IndependentSums.gammaTriangleConst 1 *
      (layerDiagonalAllGapConst d * base) :=
    mul_nonneg IndependentSums.gammaTriangleConst_pos.le (mul_nonneg hC hbase)
  have hfactorSum :
      (∑ k ∈ Finset.Ioc n m,
          layerDiagonalAllGapConst d * base *
            (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ))) =
        (layerDiagonalAllGapConst d * base) *
          ∑ k ∈ Finset.Ioc n m,
            (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) := by
    rw [Finset.mul_sum]
  calc
    IndependentSums.gammaTriangleConst 1 *
          ∑ k ∈ Finset.Ioc n m,
            layerDiagonalAllGapConst d *
              (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) ≤
        IndependentSums.gammaTriangleConst 1 *
          ∑ k ∈ Finset.Ioc n m,
            layerDiagonalAllGapConst d * base *
              (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum IndependentSums.gammaTriangleConst_pos.le
    _ = (IndependentSums.gammaTriangleConst 1 *
          (layerDiagonalAllGapConst d * base)) *
        ∑ k ∈ Finset.Ioc n m,
          (3 : ℝ) ^ (-alpha * ((m - k : ℤ) : ℝ)) := by
      rw [hfactorSum]
      ring
    _ ≤ (IndependentSums.gammaTriangleConst 1 *
          (layerDiagonalAllGapConst d * base)) *
        (Homogenization.geometricDiscount alpha 1)⁻¹ :=
      mul_le_mul_of_nonneg_left hdecay hpre
    _ = layerL2DiagonalSumConst d * base := by
      unfold layerL2DiagonalSumConst
      dsimp [alpha]
      ring
    _ = layerL2DiagonalSumConst d *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := rfl

private theorem pairAmplitude_le (M : ABKModel d) (n m l : ℤ) :
    2 * (IndependentSums.gammaTriangleConst 1 *
        ∑ p ∈ layerOrderedPairs n m,
          layerPairAllGapConst d *
            (3 : ℝ) ^ (M.gamma * ((p.1 : ℝ) + (p.2 : ℝ))) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (p.2 : ℝ)))) ≤
      layerL2PairSumConst d *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := by
  let alpha : ℝ := (d : ℝ) / 2
  let base : ℝ :=
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hbase : 0 ≤ base := by dsimp [base]; positivity
  have hC : 0 ≤ layerPairAllGapConst d :=
    (layerPairAllGapConst_pos d hd).le
  have hterm : ∀ p ∈ layerOrderedPairs n m,
      layerPairAllGapConst d *
          (3 : ℝ) ^ (M.gamma * ((p.1 : ℝ) + (p.2 : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (p.2 : ℝ))) ≤
        layerPairAllGapConst d * base *
          ((3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ))) := by
    intro p hp
    have hpMem := mem_layerOrderedPairs.mp hp
    have hp1m : p.1 ≤ m := (Finset.mem_Ioc.mp hpMem.1).2
    have hp21 : p.2 < p.1 := hpMem.2.2
    have hgap1 :
        (3 : ℝ) ^ (-(2 * M.gamma + (d : ℝ) / 2) *
            ((m : ℝ) - (p.1 : ℝ))) ≤
          (3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [alpha]
      push_cast
      have hg : 0 ≤ (m : ℝ) - (p.1 : ℝ) := by
        exact_mod_cast sub_nonneg.mpr hp1m
      nlinarith [M.shellPrefix.gamma_pos]
    have hgap2 :
        (3 : ℝ) ^ (-(M.gamma + (d : ℝ) / 2) *
            ((p.1 : ℝ) - (p.2 : ℝ))) ≤
          (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [alpha]
      push_cast
      have hg : 0 ≤ (p.1 : ℝ) - (p.2 : ℝ) := by
        exact_mod_cast sub_nonneg.mpr (le_of_lt hp21)
      nlinarith [M.shellPrefix.gamma_pos]
    have hfactor := layerPairScale_factor_eq M l m p.1 p.2
    calc
      layerPairAllGapConst d *
            (3 : ℝ) ^ (M.gamma * ((p.1 : ℝ) + (p.2 : ℝ))) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (p.2 : ℝ))) =
          layerPairAllGapConst d *
            ((3 : ℝ) ^ (M.gamma * ((p.1 : ℝ) + (p.2 : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (p.2 : ℝ)))) := by
        ring
      _ = layerPairAllGapConst d *
            (base *
              (3 : ℝ) ^ (-(2 * M.gamma + (d : ℝ) / 2) *
                ((m : ℝ) - (p.1 : ℝ))) *
              (3 : ℝ) ^ (-(M.gamma + (d : ℝ) / 2) *
                ((p.1 : ℝ) - (p.2 : ℝ)))) := by
        rw [hfactor]
      _ ≤ layerPairAllGapConst d *
          (base * (3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hgap1 hbase) hgap2
            (Real.rpow_nonneg (by norm_num) _) (mul_nonneg hbase (by positivity))) hC
      _ = layerPairAllGapConst d * base *
          ((3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ))) := by ring
  have hsum := Finset.sum_le_sum hterm
  have hdecay := sum_layerOrderedPairs_twoGap_decay_le halpha n m
  have hpre : 0 ≤ 2 * IndependentSums.gammaTriangleConst 1 *
      (layerPairAllGapConst d * base) :=
    mul_nonneg (mul_nonneg (by norm_num) IndependentSums.gammaTriangleConst_pos.le)
      (mul_nonneg hC hbase)
  have hfactorSum :
      (∑ p ∈ layerOrderedPairs n m,
          layerPairAllGapConst d * base *
            ((3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
              (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ)))) =
        (layerPairAllGapConst d * base) *
          ∑ p ∈ layerOrderedPairs n m,
            ((3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
              (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ))) := by
    rw [Finset.mul_sum]
  calc
    2 * (IndependentSums.gammaTriangleConst 1 *
          ∑ p ∈ layerOrderedPairs n m,
            layerPairAllGapConst d *
              (3 : ℝ) ^ (M.gamma * ((p.1 : ℝ) + (p.2 : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (p.2 : ℝ)))) ≤
        2 * (IndependentSums.gammaTriangleConst 1 *
          ∑ p ∈ layerOrderedPairs n m,
            layerPairAllGapConst d * base *
              ((3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
                (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum IndependentSums.gammaTriangleConst_pos.le)
        (by norm_num)
    _ = (2 * IndependentSums.gammaTriangleConst 1 *
          (layerPairAllGapConst d * base)) *
        ∑ p ∈ layerOrderedPairs n m,
          ((3 : ℝ) ^ (-alpha * ((m - p.1 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (-alpha * ((p.1 - p.2 : ℤ) : ℝ))) := by
      rw [hfactorSum]
      ring
    _ ≤ (2 * IndependentSums.gammaTriangleConst 1 *
          (layerPairAllGapConst d * base)) *
        (Homogenization.geometricDiscount alpha 1)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hdecay hpre
    _ = layerL2PairSumConst d * base := by
      unfold layerL2PairSumConst
      dsimp [alpha]
      ring
    _ = layerL2PairSumConst d *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := rfl

/-- The sum of the centered diagonal shell masses has the terminal all-gap
scale. -/
theorem diagonalFiniteShellMassSum_isBigO_allGap
    (M : ABKModel d) {n m l : ℤ} (hnm : n < m) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
        (cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
            (Disorder.cstarPlus M * Real.log 3)))
      (layerL2DiagonalSumConst d *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))))) := by
  have hs : (Finset.Ioc n m).Nonempty := by
    exact ⟨m, Finset.mem_Ioc.mpr ⟨hnm, le_rfl⟩⟩
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (s := Finset.Ioc n m)
    (X := fun (k : ℤ) (omega : ShellSeq d) =>
      cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (Disorder.cstarPlus M * Real.log 3))
    (a := fun k => layerDiagonalAllGapConst d *
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))))
    (σ := 1) (by norm_num) hs
    (fun _ _ => mul_pos
      (mul_pos (layerDiagonalAllGapConst_pos d) (by positivity)) (by positivity))
    (fun k _ =>
      isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_exactMean_allGap
        M k l)
    (fun k _ => (measurable_cubeFrobeniusMassFiniteShellIncrement
      (d := d) l (k - 1) k).sub measurable_const)
  exact hfinite.mono_scale (diagonalAmplitude_le M n m l)

/-- Twice the ordered off-diagonal pairing sum has the terminal all-gap scale. -/
theorem two_mul_pairFiniteShellMassSum_isBigO_allGap
    (M : ABKModel d) (n m l : ℤ) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d => 2 * ∑ p ∈ layerOrderedPairs n m,
        cubeFrobeniusPairingReg (originCube d l)
          (finiteShellIncrement omega (p.1 - 1) p.1)
          (finiteShellIncrement omega (p.2 - 1) p.2))
      (layerL2PairSumConst d *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  by_cases hs : (layerOrderedPairs n m).Nonempty
  · have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (s := layerOrderedPairs n m)
      (X := fun (p : ℤ × ℤ) (omega : ShellSeq d) =>
        cubeFrobeniusPairingReg (originCube d l)
          (finiteShellIncrement omega (p.1 - 1) p.1)
          (finiteShellIncrement omega (p.2 - 1) p.2))
      (a := fun p => layerPairAllGapConst d *
        (3 : ℝ) ^ (M.gamma * ((p.1 : ℝ) + (p.2 : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (p.2 : ℝ))))
      (σ := 1) (by norm_num) hs
      (fun _ _ => mul_pos
        (mul_pos (layerPairAllGapConst_pos d hd) (by positivity)) (by positivity))
      (fun p hp => cubeFrobeniusPairingReg_singleShell_isBigO_allGap
        M (mem_layerOrderedPairs.mp hp).2.2)
      (fun p _ => measurable_cubeFrobeniusPairingReg_finiteShellIncrements
        (d := d) l (p.1 - 1) p.1 (p.2 - 1) p.2)
    exact (hfinite.const_mul (c := (2 : ℝ)) (by norm_num)).mono_scale
      (pairAmplitude_le M n m l)
  · have hempty : layerOrderedPairs n m = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero]
    exact isBigO_gammaSigma_zero_fun (mul_nonneg
      (layerL2PairSumConst_pos d hd).le
      (mul_nonneg (by positivity) (by positivity)))

/-- Corrected centered all-gap estimate for the literal finite-shell
Frobenius cube mass. -/
theorem cubeFrobeniusMassFiniteShellIncrement_centered_isBigO_allGap
    (M : ABKModel d) {n m l : ℤ} (hnm : n < m) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeFrobeniusMassFiniteShellIncrement l n m omega -
          ∑ k ∈ Finset.Ioc n m,
            (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
              (Disorder.cstarPlus M * Real.log 3))
      (layerL2AllGapConst d *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := by
  classical
  let base : ℝ :=
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  let D : ShellSeq d → ℝ := fun omega => ∑ k ∈ Finset.Ioc n m,
    (cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3))
  let P : ShellSeq d → ℝ := fun omega => 2 * ∑ p ∈ layerOrderedPairs n m,
    cubeFrobeniusPairingReg (originCube d l)
      (finiteShellIncrement omega (p.1 - 1) p.1)
      (finiteShellIncrement omega (p.2 - 1) p.2)
  let AD : ℝ := layerL2DiagonalSumConst d * base
  let AP : ℝ := layerL2PairSumConst d * base
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hbase : 0 < base := by dsimp [base]; positivity
  have hD : Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1) D AD := by
    simpa only [D, AD, base] using diagonalFiniteShellMassSum_isBigO_allGap M hnm
  have hP : Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1) P AP := by
    simpa only [P, AP, base] using two_mul_pairFiniteShellMassSum_isBigO_allGap M n m l
  have hDm : Measurable D := by
    dsimp [D]
    exact Finset.measurable_sum _ fun k _ =>
      (measurable_cubeFrobeniusMassFiniteShellIncrement
        (d := d) l (k - 1) k).sub measurable_const
  have hPm : Measurable P := by
    dsimp [P]
    exact (Finset.measurable_sum _ fun (p : ℤ × ℤ) _ =>
      measurable_cubeFrobeniusPairingReg_finiteShellIncrements
        (d := d) l (p.1 - 1) p.1 (p.2 - 1) p.2).const_mul 2
  let X : Fin 2 → ShellSeq d → ℝ := ![D, P]
  let a : Fin 2 → ℝ := ![AD, AP]
  have hX : ∀ i : Fin 2,
      Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1) (X i) (a i) := by
    intro i
    fin_cases i
    · simpa only [X, a, Matrix.cons_val_zero] using hD
    · simpa only [X, a, Matrix.cons_val_one, Matrix.head_cons] using hP
  have hXm : ∀ i : Fin 2, Measurable (X i) := by
    intro i
    fin_cases i
    · simpa only [X, Matrix.cons_val_zero] using hDm
    · simpa only [X, Matrix.cons_val_one, Matrix.head_cons] using hPm
  have ha : ∀ i : Fin 2, 0 < a i := by
    intro i
    fin_cases i
    · simpa only [a, AD] using mul_pos (layerL2DiagonalSumConst_pos d hd) hbase
    · simpa only [a, AP, Matrix.cons_val_one, Matrix.head_cons] using
        mul_pos (layerL2PairSumConst_pos d hd) hbase
  have htri := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (s := (Finset.univ : Finset (Fin 2)))
    (X := X) (a := a) (σ := 1) (by norm_num) Finset.univ_nonempty
    (fun i _ => ha i) (fun i _ => hX i) (fun i _ => hXm i)
  have hsum : (fun omega => ∑ i : Fin 2, X i omega) =
      fun omega => D omega + P omega := by
    funext omega
    rw [Fin.sum_univ_two]
    simp only [X, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hascale : IndependentSums.gammaTriangleConst 1 * ∑ i : Fin 2, a i =
      layerL2AllGapConst d * base := by
    rw [Fin.sum_univ_two]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp [AD, AP, layerL2AllGapConst]
    ring
  rw [hsum, hascale] at htri
  have heq : ∀ omega : ShellSeq d,
      cubeFrobeniusMassFiniteShellIncrement l n m omega -
          ∑ k ∈ Finset.Ioc n m,
            (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
              (Disorder.cstarPlus M * Real.log 3) =
        D omega + P omega := by
    intro omega
    rw [cubeFrobeniusMassFiniteShellIncrement_eq_diagonal_add_pairs]
    dsimp only [D, P]
    rw [Finset.sum_sub_distrib]
    ring
  apply (Book.Ch04.isBigO_congr_ae
    (Filter.Eventually.of_forall heq)).mpr
  simpa only [base, mul_assoc] using htri

end

end Algsuperdiff.Section3.Provider.Stream
