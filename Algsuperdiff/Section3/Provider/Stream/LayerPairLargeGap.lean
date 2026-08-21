import Algsuperdiff.Section3.Provider.Stream.LayerPairProduct

/-!
# Deterministic simplification of the corrected large-gap shell pair

This internal module evaluates the color count and descendant cardinality and
absorbs the fixed partition-normalization shift into a dimension-only
constant.  It is the large-gap half of the corrected off-diagonal argument.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Orlicz

noncomputable section

variable {d : ℕ}

/-- Dimension-only amplitude for a corrected large-gap shell pair. -/
def layerPairLargeConst (d : ℕ) : ℝ :=
  Book.Ch04.gammaProductConst 2 2 * Book.Ch04.gammaTriangleConst 2 *
    (((scaleColorPeriod 0) ^ d : ℕ) : ℝ) * weightedSubgaussianConst *
    (4 * (d : ℝ) ^ 2 * singleShellLpMassConst d) *
    (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ))

theorem layerPairLargeConst_pos (d : ℕ) (hd : 0 < d) :
    0 < layerPairLargeConst d := by
  have hcolor : 0 < (((scaleColorPeriod 0) ^ d : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (scaleColorPeriod_pos 0) d
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hproduct : 0 < Book.Ch04.gammaProductConst 2 2 := by
    unfold Book.Ch04.gammaProductConst
    positivity
  have hshift : 0 <
      (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) := by
    positivity
  have htriangle : 0 < Book.Ch04.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hcore : 0 < 4 * (d : ℝ) ^ 2 * singleShellLpMassConst d :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hdR))
      (singleShellLpMassConst_pos d)
  unfold layerPairLargeConst
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos
          (mul_pos hproduct htriangle) hcolor)
        weightedSubgaussianConst_pos)
      hcore)
    hshift

/-- One-shell norm scales have the expected log-free geometric amplitude. -/
theorem streamIncrementLpNormScale_two_singleShell_le
    (M : ABKModel d) (k : ℤ) :
    streamIncrementLpNormScale M 2 (k - 1) k ≤
      Real.sqrt (singleShellLpMassConst d) *
        (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
  have hmass := streamIncrementLpMassScale_two_singleShell_le M k
  have hconst0 : 0 ≤ singleShellLpMassConst d :=
    (singleShellLpMassConst_pos d).le
  unfold streamIncrementLpNormScale
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  calc
    Real.sqrt (streamIncrementLpMassScale M 2 (k - 1) k) ≤
        Real.sqrt (singleShellLpMassConst d *
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := Real.sqrt_le_sqrt hmass
    _ = Real.sqrt (singleShellLpMassConst d) *
        Real.sqrt ((3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
      rw [Real.sqrt_mul hconst0]
    _ = Real.sqrt (singleShellLpMassConst d) *
        (3 : ℝ) ^ (M.gamma * (k : ℝ)) := by
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring

/-- The raw product scale is bounded by the source-shaped large-gap scale. -/
theorem layerPairLargeGapScale_le_source
    (M : ABKModel d) {k k' l : ℤ}
    (hgap : k' + (incrementPartitionShift d : ℤ) ≤ l) :
    layerPairLargeGapScale M k k' l ≤
      layerPairLargeConst d *
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) := by
  let shift : ℤ := incrementPartitionShift d
  let j : ℤ := l - (k' + shift)
  let Q : TriadicCube d := originCube d j
  let N : ℝ := ((descendantsAtScale Q 0).card : ℝ)
  let colors : ℝ :=
    (((descendantsAtScale Q 0).image (cubeScaleColor 0)).card : ℝ)
  let Klo : ℝ := streamIncrementLpNormScale M 2 (k' - 1) k'
  let Kup : ℝ := streamIncrementLpNormScale M 2 (k - 1) k
  have hj : 0 ≤ j := by dsimp [j, shift]; omega
  have hNpos : 0 < N := by
    dsimp [N, Q]
    exact_mod_cast (descendantsAtScale_nonempty (originCube d j) (by
      change 0 ≤ j
      exact hj)).card_pos
  have hcolor : colors ≤ (((scaleColorPeriod 0) ^ d : ℕ) : ℝ) := by
    dsimp [colors, Q]
    exact_mod_cast card_image_cubeScaleColor_descendantsAtScale_le
      (originCube d j) 0
  have hKlo := streamIncrementLpNormScale_two_singleShell_le M k'
  have hKup := streamIncrementLpNormScale_two_singleShell_le M k
  have hKlo0 : 0 ≤ Klo := by
    dsimp [Klo, streamIncrementLpNormScale]
    exact Real.rpow_nonneg
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)).le _
  have hKup0 : 0 ≤ Kup := by
    dsimp [Kup, streamIncrementLpNormScale]
    exact Real.rpow_nonneg
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)).le _
  have hKprod : Klo * Kup ≤ singleShellLpMassConst d *
      (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) := by
    calc
      Klo * Kup ≤
          (Real.sqrt (singleShellLpMassConst d) *
              (3 : ℝ) ^ (M.gamma * (k' : ℝ))) *
            (Real.sqrt (singleShellLpMassConst d) *
              (3 : ℝ) ^ (M.gamma * (k : ℝ))) :=
        mul_le_mul (by simpa only [Klo] using hKlo)
          (by simpa only [Kup] using hKup) hKup0
          (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
      _ = singleShellLpMassConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) := by
        rw [show
            Real.sqrt (singleShellLpMassConst d) *
                (3 : ℝ) ^ (M.gamma * (k' : ℝ)) *
              (Real.sqrt (singleShellLpMassConst d) *
                (3 : ℝ) ^ (M.gamma * (k : ℝ))) =
              (Real.sqrt (singleShellLpMassConst d) ^ 2) *
                ((3 : ℝ) ^ (M.gamma * (k' : ℝ)) *
                  (3 : ℝ) ^ (M.gamma * (k : ℝ))) by ring,
          Real.sq_sqrt (singleShellLpMassConst_pos d).le,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring_nf
  have hcard : N⁻¹ * Real.sqrt N =
      (3 : ℝ) ^ (-((d : ℝ) / 2) * (j : ℝ)) := by
    rw [show N⁻¹ * Real.sqrt N = Book.Ch04.partitionCardinalityScale
        (d := d) 0 j by
      unfold Book.Ch04.partitionCardinalityScale
      dsimp only [N, Q]
      rw [div_eq_mul_inv]
      ring,
      partitionCardinalityScale_originCube_zero (d := d) hj]
  have hshift :
      (3 : ℝ) ^ (-((d : ℝ) / 2) * (j : ℝ)) =
        (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    dsimp [j, shift]
    push_cast
    ring
  have hbase0 : 0 ≤ Book.Ch04.gammaProductConst 2 2 *
      Book.Ch04.gammaTriangleConst 2 * weightedSubgaussianConst *
      (4 * (d : ℝ) ^ 2) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_pos_of_pos (by norm_num) _).le
          IndependentSums.gammaTriangleConst_pos.le)
        weightedSubgaussianConst_pos.le)
      (mul_nonneg (by norm_num) (sq_nonneg _))
  calc
    layerPairLargeGapScale M k k' l =
        (Book.Ch04.gammaProductConst 2 2 * Book.Ch04.gammaTriangleConst 2 *
          weightedSubgaussianConst * (4 * (d : ℝ) ^ 2)) *
          colors * (Klo * Kup) * (N⁻¹ * Real.sqrt N) := by
      unfold layerPairLargeGapScale layerPairUpperDeterministicScale
      unfold layerPairCommonCoeff
      dsimp only [Q, j, shift, N, colors, Klo, Kup]
      ring
    _ ≤ (Book.Ch04.gammaProductConst 2 2 * Book.Ch04.gammaTriangleConst 2 *
          weightedSubgaussianConst * (4 * (d : ℝ) ^ 2)) *
          (((scaleColorPeriod 0) ^ d : ℕ) : ℝ) *
          (singleShellLpMassConst d *
            (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ)))) *
          (N⁻¹ * Real.sqrt N) := by
      gcongr
    _ = layerPairLargeConst d *
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) := by
      rw [hcard, hshift]
      unfold layerPairLargeConst
      ring

/-- Source-shaped corrected large-gap fixed-pair concentration. -/
theorem cubeFrobeniusPairingReg_singleShell_isBigO_largeGap_sharp
    (M : ABKModel d) {k k' l : ℤ} (hne : k ≠ k')
    (hgap : k' + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega => cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega (k - 1) k)
        (finiteShellIncrement omega (k' - 1) k'))
      (layerPairLargeConst d *
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ)))) :=
  (cubeFrobeniusPairingReg_singleShell_isBigO_largeGap M hne hgap).mono_scale
    (layerPairLargeGapScale_le_source M hgap)

end

end Algsuperdiff.Section3.Provider.Stream
