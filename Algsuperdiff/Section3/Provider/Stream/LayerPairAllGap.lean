import Algsuperdiff.Section3.Provider.Orlicz.ProductPower
import Algsuperdiff.Section3.Provider.Stream.LayerPairLargeGap

/-!
# All-gap corrected off-diagonal shell pairing

The large-gap branch uses the frozen-field coloring argument.  In the bounded
short-gap branch, a direct product of the two cube norms is sufficient because
the missing spatial gain is uniformly absorbed by the fixed normalization
shift.  This module is internal provider infrastructure.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Dimension-only amplitude for the direct short-gap pair estimate. -/
def layerPairShortConst (d : ℕ) : ℝ :=
  Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2 *
    singleShellLpMassConst d *
    (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ))

/-- Direct product-tail bound for one off-diagonal pair. -/
theorem cubeFrobeniusPairingReg_singleShell_isBigO_product
    (M : ABKModel d) (k k' l : ℤ) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega => cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega (k - 1) k)
        (finiteShellIncrement omega (k' - 1) k'))
      (Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2 *
        streamIncrementLpNormScale M 2 (k - 1) k *
        streamIncrementLpNormScale M 2 (k' - 1) k') := by
  let X : ShellSeq d → ℝ :=
    cubeStreamIncrementLpNorm 2 (originCube d l) (k - 1) k
  let Y : ShellSeq d → ℝ :=
    cubeStreamIncrementLpNorm 2 (originCube d l) (k' - 1) k'
  let A : ℝ := streamIncrementLpNormScale M 2 (k - 1) k
  let B : ℝ := streamIncrementLpNormScale M 2 (k' - 1) k'
  have hA : 0 ≤ A := by
    dsimp [A, streamIncrementLpNormScale]
    exact Real.rpow_nonneg
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)).le _
  have hB : 0 ≤ B := by
    dsimp [B, streamIncrementLpNormScale]
    exact Real.rpow_nonneg
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)).le _
  have hX := isBigOWith_gammaSigma_cubeStreamIncrementLpNorm
    M (p := 2) (by norm_num) (by omega : k - 1 < k) (originCube d l)
  have hY := isBigOWith_gammaSigma_cubeStreamIncrementLpNorm
    M (p := 2) (by norm_num) (by omega : k' - 1 < k') (originCube d l)
  have hprod := Book.Ch04.isBigOWith_gammaSigma_mul
    (μ := M.P.toMeasure) (X := X) (Y := Y) (A := A) (B := B)
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    hA hB
    (fun omega => cubeStreamIncrementLpNorm_nonneg
      (d := d) (p := 2) (by norm_num) _ _ _ omega)
    (fun omega => cubeStreamIncrementLpNorm_nonneg
      (d := d) (p := 2) (by norm_num) _ _ _ omega)
    (by simpa only [X, A] using hX) (by simpa only [Y, B] using hY)
  have hscaled := (hprod.const_mul (sq_nonneg (d : ℝ))).of_le fun omega => by
    have hk := sqrt_cubeFrobeniusMassReg_finiteShellIncrement_le
      (originCube d l) (k - 1) k omega
    have hk' := sqrt_cubeFrobeniusMassReg_finiteShellIncrement_le
      (originCube d l) (k' - 1) k' omega
    have hpair := abs_cubeFrobeniusPairingReg_le
      (originCube d l)
      (finiteShellIncrement omega (k - 1) k)
      (finiteShellIncrement omega (k' - 1) k')
      (fun i j => continuous_finiteShellIncrement_entry omega (k - 1) k i j)
      (fun i j => continuous_finiteShellIncrement_entry omega (k' - 1) k' i j)
    calc
      |cubeFrobeniusPairingReg (originCube d l)
          (finiteShellIncrement omega (k - 1) k)
          (finiteShellIncrement omega (k' - 1) k')| ≤
          Real.sqrt (cubeFrobeniusMassReg (originCube d l)
            (finiteShellIncrement omega (k - 1) k)) *
          Real.sqrt (cubeFrobeniusMassReg (originCube d l)
            (finiteShellIncrement omega (k' - 1) k')) := hpair
      _ ≤ ((d : ℝ) * X omega) * ((d : ℝ) * Y omega) :=
        mul_le_mul hk hk' (Real.sqrt_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _)
            (cubeStreamIncrementLpNorm_nonneg (by norm_num) _ _ _ _))
      _ = (d : ℝ) ^ 2 * (X omega * Y omega) := by ring
  change IndependentSums.IsBigOWith M.P.toMeasure
    (IndependentSums.gammaSigma 1)
    (fun omega => |cubeFrobeniusPairingReg (originCube d l)
      (finiteShellIncrement omega (k - 1) k)
      (finiteShellIncrement omega (k' - 1) k')|)
    (Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2 *
      streamIncrementLpNormScale M 2 (k - 1) k *
      streamIncrementLpNormScale M 2 (k' - 1) k')
  simpa only [show (2 : ℝ) * 2 / (2 + 2) = 1 by norm_num,
    X, Y, A, B, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Source-shaped direct estimate in the bounded short-gap regime. -/
theorem cubeFrobeniusPairingReg_singleShell_isBigO_shortGap
    (M : ABKModel d) {k k' l : ℤ}
    (hshort : l < k' + (incrementPartitionShift d : ℤ)) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega => cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega (k - 1) k)
        (finiteShellIncrement omega (k' - 1) k'))
      (layerPairShortConst d *
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ)))) := by
  have hraw := cubeFrobeniusPairingReg_singleShell_isBigO_product M k k' l
  apply hraw.mono_scale
  have hK := streamIncrementLpNormScale_two_singleShell_le M k
  have hK' := streamIncrementLpNormScale_two_singleShell_le M k'
  have hK0 : 0 ≤ streamIncrementLpNormScale M 2 (k - 1) k := by
    unfold streamIncrementLpNormScale
    exact Real.rpow_nonneg
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)).le _
  have hK'0 : 0 ≤ streamIncrementLpNormScale M 2 (k' - 1) k' := by
    unfold streamIncrementLpNormScale
    exact Real.rpow_nonneg
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)).le _
  have hprod : streamIncrementLpNormScale M 2 (k - 1) k *
      streamIncrementLpNormScale M 2 (k' - 1) k' ≤
      singleShellLpMassConst d *
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) := by
    calc
      streamIncrementLpNormScale M 2 (k - 1) k *
          streamIncrementLpNormScale M 2 (k' - 1) k' ≤
        (Real.sqrt (singleShellLpMassConst d) *
            (3 : ℝ) ^ (M.gamma * (k : ℝ))) *
          (Real.sqrt (singleShellLpMassConst d) *
            (3 : ℝ) ^ (M.gamma * (k' : ℝ))) :=
        mul_le_mul hK hK' hK'0
          (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
      _ = singleShellLpMassConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) := by
        rw [show
            Real.sqrt (singleShellLpMassConst d) *
                (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
              (Real.sqrt (singleShellLpMassConst d) *
                (3 : ℝ) ^ (M.gamma * (k' : ℝ))) =
              Real.sqrt (singleShellLpMassConst d) ^ 2 *
                ((3 : ℝ) ^ (M.gamma * (k : ℝ)) *
                  (3 : ℝ) ^ (M.gamma * (k' : ℝ))) by ring,
          Real.sq_sqrt (singleShellLpMassConst_pos d).le,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring_nf
  have hgap : 0 ≤ (incrementPartitionShift d : ℝ) -
      ((l : ℝ) - (k' : ℝ)) := by
    have hz : l - k' ≤ (incrementPartitionShift d : ℤ) := by omega
    have hr : (l : ℝ) - (k' : ℝ) ≤
        (incrementPartitionShift d : ℝ) := by exact_mod_cast hz
    linarith
  have hone : (1 : ℝ) ≤
      (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.one_le_rpow (by norm_num)
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
  have hpre : 0 ≤ Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2 := by
    exact mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le (sq_nonneg _)
  calc
    Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2 *
        streamIncrementLpNormScale M 2 (k - 1) k *
        streamIncrementLpNormScale M 2 (k' - 1) k' =
      (Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2) *
        (streamIncrementLpNormScale M 2 (k - 1) k *
          streamIncrementLpNormScale M 2 (k' - 1) k') := by ring
    _ ≤ (Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2) *
        (singleShellLpMassConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ)))) :=
      mul_le_mul_of_nonneg_left hprod hpre
    _ ≤ (Book.Ch04.gammaProductConst 2 2 * (d : ℝ) ^ 2) *
        (singleShellLpMassConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ)))) *
        ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ)))) := by
      exact le_mul_of_one_le_right
        (mul_nonneg hpre
          (mul_nonneg (singleShellLpMassConst_pos d).le (by positivity))) hone
    _ = layerPairShortConst d *
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) := by
      unfold layerPairShortConst
      ring

/-- One dimension-only amplitude for both off-diagonal scale branches. -/
def layerPairAllGapConst (d : ℕ) : ℝ :=
  max (layerPairShortConst d) (layerPairLargeConst d)

theorem layerPairAllGapConst_pos (d : ℕ) (hd : 0 < d) :
    0 < layerPairAllGapConst d :=
  (layerPairLargeConst_pos d hd).trans_le (le_max_right _ _)

/-- Corrected all-gap fixed-pair concentration for ordered distinct shells. -/
theorem cubeFrobeniusPairingReg_singleShell_isBigO_allGap
    (M : ABKModel d) {k k' l : ℤ} (hk'k : k' < k) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega => cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega (k - 1) k)
        (finiteShellIncrement omega (k' - 1) k'))
      (layerPairAllGapConst d *
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ)))) := by
  by_cases hlarge : k' + (incrementPartitionShift d : ℤ) ≤ l
  · have hraw := cubeFrobeniusPairingReg_singleShell_isBigO_largeGap_sharp
      (d := d) M (k := k) (k' := k') (l := l) (ne_of_gt hk'k) hlarge
    have hgeom : 0 ≤
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) :=
      mul_nonneg (by positivity) (by positivity)
    have hscale : layerPairLargeConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) ≤
        layerPairAllGapConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (le_max_right _ _) hgeom
    exact hraw.mono_scale hscale
  · have hraw := cubeFrobeniusPairingReg_singleShell_isBigO_shortGap
      (d := d) M (k := k) (k' := k') (l := l) (lt_of_not_ge hlarge)
    have hgeom : 0 ≤
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) :=
      mul_nonneg (by positivity) (by positivity)
    have hscale : layerPairShortConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) ≤
        layerPairAllGapConst d *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + (k' : ℝ))) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k' : ℝ))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (le_max_left _ _) hgeom
    exact hraw.mono_scale hscale

end

end Algsuperdiff.Section3.Provider.Stream
