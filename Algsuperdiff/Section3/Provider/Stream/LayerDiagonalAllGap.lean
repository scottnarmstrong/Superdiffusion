import Algsuperdiff.Section3.Provider.Stream.LayerDiagonalConcentration

/-!
# All-gap diagonal concentration for one stream shell

This module supplies the short-gap companion to
`LayerDiagonalConcentration` and combines the two scale branches.  It remains
ordinary provider infrastructure for the diagonal part of the corrected
proof of ABK26's `e.km.kn.L2.bound`; the off-diagonal two-shell pairing is a
separate input.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Filter MeasureTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The half-open Frobenius cube mass is pointwise nonnegative. -/
theorem cubeFrobeniusMassFiniteShellIncrement_nonneg
    (l n m : ℤ) (omega : ShellSeq d) :
    0 ≤ cubeFrobeniusMassFiniteShellIncrement l n m omega := by
  unfold cubeFrobeniusMassFiniteShellIncrement cubeAverage
  exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos _).le)
    (integral_nonneg fun x => matrixFrobeniusNormSq_nonneg _)

/-- Frobenius mass is bounded by `d²` times the operator-norm square mass. -/
theorem cubeFrobeniusMassFiniteShellIncrement_le_mul_streamIncrementLpMass_two
    (l n m : ℤ) (omega : ShellSeq d) :
    cubeFrobeniusMassFiniteShellIncrement l n m omega ≤
      (d : ℝ) ^ 2 * streamIncrementLpMass 2 l n m omega := by
  rw [cubeFrobeniusMassFiniteShellIncrement_eq_sum_entrySq]
  calc
    (∑ p : Fin d × Fin d,
        cubeAverageFiniteShellEntrySq l n m p.1 p.2 omega)
        ≤ ∑ _p : Fin d × Fin d,
            streamIncrementLpMass 2 l n m omega := by
          exact Finset.sum_le_sum fun p _ =>
            cubeAverageFiniteShellEntrySq_le_streamIncrementLpMass_two
              l n m p.1 p.2 omega
    _ = (d : ℝ) ^ 2 * streamIncrementLpMass 2 l n m omega := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_prod, Fintype.card_fin]
          push_cast
          ring

private theorem partitionStreamIncrementLaw_entrySqMean_le_massScale
    (M : ABKModel d) (k : ℤ) (i j : Fin d) :
    (∫ a, regFieldEntrySqMassRep i j (cubeSet (originCube d 0)) a
        ∂(partitionStreamIncrementLaw M (k - 1) k)) ≤
      streamIncrementLpMassScale M 2 (k - 1) k := by
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d k) (incrementPartitionScale_ne_zero d k)
      (finiteShellIncrement omega (k - 1) k)
  let g : RegCoeffField d → ℝ :=
    regFieldEntrySqMassRep i j (cubeSet (originCube d 0))
  have hF : Measurable F :=
    measurable_partitionIncrementField (d := d) (k - 1) k
  have hg : Measurable g := measurable_regFieldEntrySqMassRep _ i j
  have hread : ∀ omega, g (F omega) =
      cubeAverageFiniteShellEntrySq
        (k + (incrementPartitionShift d : ℤ)) (k - 1) k i j omega := by
    intro omega
    exact regFieldEntrySqMassRep_originCube_zero_partitionIncrement
      i j (k - 1) k omega
  have hle : ∀ omega, g (F omega) ≤
      streamIncrementLpMass 2 (k + (incrementPartitionShift d : ℤ))
        (k - 1) k omega := by
    intro omega
    rw [hread omega]
    exact cubeAverageFiniteShellEntrySq_le_streamIncrementLpMass_two
      _ _ _ i j omega
  have hstreamInt : Integrable
      (streamIncrementLpMass 2 (k + (incrementPartitionShift d : ℤ))
        (k - 1) k) M.P.toMeasure :=
    integrable_streamIncrementLpMass M (by norm_num) (by omega) _
  have hcompInt : Integrable (fun omega => g (F omega)) M.P.toMeasure := by
    refine Integrable.mono' hstreamInt (hg.comp hF).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (regFieldEntrySqMassRep_nonneg i j _ (F omega))]
    exact hle omega
  rw [partitionStreamIncrementLaw_eq_map,
    integral_map hF.aemeasurable hg.aestronglyMeasurable]
  exact (integral_mono hcompInt hstreamInt hle).trans
    (integral_streamIncrementLpMass_le_massScale M (by norm_num) (by omega) _)

private theorem exactSingleShellMean_le_mul_massScale
    (M : ABKModel d) (k : ℤ) :
    (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) ≤
      (d : ℝ) ^ 2 * streamIncrementLpMassScale M 2 (k - 1) k := by
  rw [← sum_partitionStreamIncrementLaw_entrySqMeans_eq M k]
  calc
    (∑ p : Fin d × Fin d,
        ∫ a, regFieldEntrySqMassRep p.1 p.2 (cubeSet (originCube d 0)) a
          ∂(partitionStreamIncrementLaw M (k - 1) k))
        ≤ ∑ _p : Fin d × Fin d,
            streamIncrementLpMassScale M 2 (k - 1) k := by
          exact Finset.sum_le_sum fun p _ =>
            partitionStreamIncrementLaw_entrySqMean_le_massScale
              M k p.1 p.2
    _ = (d : ℝ) ^ 2 * streamIncrementLpMassScale M 2 (k - 1) k := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            Fintype.card_prod, Fintype.card_fin]
          push_cast
          ring

/-- A dimension-only constant for the bounded short-gap branch. -/
noncomputable def layerDiagonalSmallConst (d : ℕ) : ℝ :=
  1 + (d : ℝ) ^ 2 * singleShellLpMassConst d *
    (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ))

theorem layerDiagonalSmallConst_pos (d : ℕ) :
    0 < layerDiagonalSmallConst d := by
  unfold layerDiagonalSmallConst
  apply add_pos_of_pos_of_nonneg zero_lt_one
  exact mul_nonneg
    (mul_nonneg (sq_nonneg (d : ℝ)) (singleShellLpMassConst_pos d).le)
    (Real.rpow_pos_of_pos (by norm_num) _).le

/-- The centered diagonal one-shell mass on the bounded short-gap branch. -/
theorem isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_exactMean_shortGap
    (M : ABKModel d) (k : ℤ) {l : ℤ}
    (hshort : l < k + (incrementPartitionShift d : ℤ)) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
            (Disorder.cstarPlus M * Real.log 3))
      (layerDiagonalSmallConst d *
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ)))) := by
  let K : ℝ := streamIncrementLpMassScale M 2 (k - 1) k
  let c : ℝ := (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
    (Disorder.cstarPlus M * Real.log 3)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
      (mul_nonneg (Disorder.cstarPlus_nonneg M)
        (Real.log_nonneg (by norm_num)))
  have hcK : c ≤ (d : ℝ) ^ 2 * K := by
    exact exactSingleShellMean_le_mul_massScale M k
  have hraw : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 1)
      (cubeFrobeniusMassFiniteShellIncrement l (k - 1) k)
      ((d : ℝ) ^ 2 * K) := by
    have hmass : IndependentSums.IsBigOWith M.P.toMeasure
        (IndependentSums.gammaSigma 1)
        (streamIncrementLpMass 2 l (k - 1) k) K := by
      simpa only [show (2 : ℝ) / 2 = 1 by norm_num, K] using
        isBigOWith_gammaSigma_streamIncrementLpMass
          M (p := 2) (by norm_num) (by omega) l
    exact (hmass.const_mul (sq_nonneg (d : ℝ))).of_le fun omega =>
      cubeFrobeniusMassFiniteShellIncrement_le_mul_streamIncrementLpMass_two
        l (k - 1) k omega
  have hcenter : Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega - c)
      ((d : ℝ) ^ 2 * K) :=
    isBigO_sub_const_of_isBigOWith_of_nonneg hc0 hcK
      (cubeFrobeniusMassFiniteShellIncrement_nonneg l (k - 1) k) hraw
  apply hcenter.mono_scale
  have hmassScale := streamIncrementLpMassScale_two_singleShell_le M k
  have hgeom : 0 ≤ (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by positivity
  have hgain : 0 ≤ (3 : ℝ) ^
      (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by positivity
  have hgap : (0 : ℝ) ≤
      (incrementPartitionShift d : ℝ) - ((l : ℝ) - (k : ℝ)) := by
    have : l - k ≤ (incrementPartitionShift d : ℤ) := by omega
    have hcast : (l : ℝ) - (k : ℝ) ≤
        (incrementPartitionShift d : ℝ) := by exact_mod_cast this
    linarith
  have hone : (1 : ℝ) ≤
      (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.one_le_rpow (by norm_num)
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
  calc
    (d : ℝ) ^ 2 * K ≤
        ((d : ℝ) ^ 2 * singleShellLpMassConst d) *
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
      simpa only [K, mul_assoc] using
        mul_le_mul_of_nonneg_left hmassScale (sq_nonneg (d : ℝ))
    _ ≤ ((d : ℝ) ^ 2 * singleShellLpMassConst d *
          (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ))) *
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by
      have hrawConst : 0 ≤ (d : ℝ) ^ 2 * singleShellLpMassConst d := by
        exact mul_nonneg (sq_nonneg (d : ℝ))
          (singleShellLpMassConst_pos d).le
      calc
        (d : ℝ) ^ 2 * singleShellLpMassConst d *
            (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))
            ≤ ((d : ℝ) ^ 2 * singleShellLpMassConst d) *
              ((3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
                ((3 : ℝ) ^ (((d : ℝ) / 2) *
                    (incrementPartitionShift d : ℝ)) *
                  (3 : ℝ) ^ (-((d : ℝ) / 2) *
                    ((l : ℝ) - (k : ℝ))))) := by
              exact mul_le_mul_of_nonneg_left
                (le_mul_of_one_le_right hgeom hone) hrawConst
        _ = _ := by ring
    _ ≤ layerDiagonalSmallConst d *
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ hgain
      apply mul_le_mul_of_nonneg_right _ hgeom
      unfold layerDiagonalSmallConst
      linarith

/-- One dimension-only envelope for both diagonal scale branches. -/
noncomputable def layerDiagonalAllGapConst (d : ℕ) : ℝ :=
  max (layerDiagonalSmallConst d) (layerDiagonalLargeConst d)

theorem layerDiagonalAllGapConst_pos (d : ℕ) :
    0 < layerDiagonalAllGapConst d :=
  lt_of_lt_of_le (layerDiagonalSmallConst_pos d) (le_max_left _ _)

/-- All-gap diagonal one-shell concentration, in particular on every source
scale `k ≤ l`. -/
theorem isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_exactMean_allGap
    (M : ABKModel d) (k : ℤ) (l : ℤ) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
            (Disorder.cstarPlus M * Real.log 3))
      (layerDiagonalAllGapConst d *
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ)))) := by
  by_cases hlarge : k + (incrementPartitionShift d : ℤ) ≤ l
  · exact
      (isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_exactMean_sharp
        M k hlarge).mono_scale (by
          have hgeom : 0 ≤ (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
            positivity
          have hgain : 0 ≤ (3 : ℝ) ^
              (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by
            positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hgeom) hgain)
  · exact
      (isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_exactMean_shortGap
        M k (by omega)).mono_scale (by
          have hgeom : 0 ≤ (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
            positivity
          have hgain : 0 ≤ (3 : ℝ) ^
              (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by
            positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hgeom) hgain)

end

end Algsuperdiff.Section3.Provider.Stream
