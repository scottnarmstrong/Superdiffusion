import Algsuperdiff.Section3.Provider.Stream.LayerPairColor
import Homogenization.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# Colored descendant averages for a frozen coarser field

This internal module recombines the restriction-unit-range color classes from
`LayerPairColor`.  The estimate first sums the actual frozen cell masses in
each color and only then compares with the parent mass.  Thus it retains the
square-root descendant-count gain needed by the corrected two-shell argument.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Orlicz

noncomputable section

variable {d : ℕ}

/-- The common positive scale used to recombine the nonempty color classes. -/
def frozenDescendantPairingColorScale (M : ABKModel d) (k' : ℤ)
    (Q : TriadicCube d) (a : RegCoeffField d) : ℝ :=
  weightedSubgaussianConst *
    (4 * (d : ℝ) * streamIncrementLpNormScale M 2 (k' - 1) k' *
      ((descendantsAtScale Q 0).card : ℝ)⁻¹ *
      Real.sqrt
        (((descendantsAtScale Q 0).card : ℝ) *
          cubeFrobeniusMassReg Q a))

/-- The exact weighted scale of any color class is bounded by the common
parent-mass scale. -/
theorem frozenColorPairingVarianceScale_le_parent
    (M : ABKModel d) (k' : ℤ) (Q : TriadicCube d) (hQ : 0 ≤ Q.scale)
    (c : ScaleColor d 0) (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j) :
    frozenColorPairingVarianceScale M k' Q c a ≤
      frozenDescendantPairingColorScale M k' Q a := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let S : Finset (TriadicCube d) := descendantsAtScaleScaleColorClass Q 0 c
  let N : ℝ := (D.card : ℝ)
  let K : ℝ := streamIncrementLpNormScale M 2 (k' - 1) k'
  have hmass (R : TriadicCube d) : 0 ≤ cubeFrobeniusMassReg R a := by
    unfold cubeFrobeniusMassReg cubeAverage
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos R).le)
      (integral_nonneg fun x => matrixFrobeniusNormSq_nonneg _)
  have hclass :
      ∑ R ∈ S, cubeFrobeniusMassReg R a ≤
        ∑ R ∈ D, cubeFrobeniusMassReg R a := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro R hR
      exact (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1
    · intro R _ _
      exact hmass R
  have hsum :
      ∑ R ∈ D, cubeFrobeniusMassReg R a =
        N * cubeFrobeniusMassReg Q a := by
    simpa only [D, N] using
      sum_cubeFrobeniusMassReg_descendantsAtScale Q hQ a ha
  have hfactor_nonneg :
      0 ≤ 4 * (d : ℝ) * K * N⁻¹ := by
    have hK : 0 < K := by
      dsimp [K]
      unfold streamIncrementLpNormScale
      exact Real.rpow_pos_of_pos
        (streamIncrementLpMassScale_pos M (by norm_num) (by omega)) _
    positivity
  have hinside :
      (∑ R ∈ S, N⁻¹ ^ 2 *
          (16 * (((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a) * K) ^ 2))) ≤
        (4 * (d : ℝ) * K * N⁻¹) ^ 2 *
          (N * cubeFrobeniusMassReg Q a) := by
    calc
      (∑ R ∈ S, N⁻¹ ^ 2 *
          (16 * (((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a) * K) ^ 2))) =
          (4 * (d : ℝ) * K * N⁻¹) ^ 2 *
            ∑ R ∈ S, cubeFrobeniusMassReg R a := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro R hR
        rw [show ((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a) * K) ^ 2 =
            (d : ℝ) ^ 2 * Real.sqrt (cubeFrobeniusMassReg R a) ^ 2 * K ^ 2 by
              ring,
          Real.sq_sqrt (hmass R)]
        ring
      _ ≤ (4 * (d : ℝ) * K * N⁻¹) ^ 2 *
          ∑ R ∈ D, cubeFrobeniusMassReg R a := by
        gcongr
      _ = (4 * (d : ℝ) * K * N⁻¹) ^ 2 *
          (N * cubeFrobeniusMassReg Q a) := by rw [hsum]
  have hsqrt := Real.sqrt_le_sqrt hinside
  rw [Real.sqrt_mul (sq_nonneg (4 * (d : ℝ) * K * N⁻¹)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg] at hsqrt
  simpa only [frozenColorPairingVarianceScale,
    frozenDescendantPairingColorScale, D, S, N, K,
    mul_assoc] using
    (mul_le_mul_of_nonneg_left hsqrt weightedSubgaussianConst_pos.le)

/-- A frozen coarser field with positive parent mass has a concentrated
normalized descendant pairing average under the finer-shell restriction law.
All proof-engineering premises remain internal to later transport to the model
law; this is not a source-facing declaration. -/
theorem frozenDescendantPairingAverage_isBigO_of_pos
    (M : ABKModel d) (k' : ℤ) (Q : TriadicCube d) (hQ : 0 ≤ Q.scale)
    (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (hmass : 0 < cubeFrobeniusMassReg Q a) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M (k' - 1) k')
      (Book.Ch04.gammaSigma 2)
      (fun b => ((descendantsAtScale Q 0).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q 0, frozenFineCellPairing a R b)
      (Book.Ch04.gammaTriangleConst 2 *
        (((descendantsAtScale Q 0).image (cubeScaleColor 0)).card : ℝ) *
        frozenDescendantPairingColorScale M k' Q a) := by
  classical
  let P : Book.Ch04.RestrictionCoeffLaw d :=
    partitionStreamIncrementLaw M (k' - 1) k'
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let colors : Finset (ScaleColor d 0) := D.image (cubeScaleColor 0)
  let Y : ScaleColor d 0 → RegCoeffField d → ℝ := fun c b =>
    ((D.card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtScaleScaleColorClass Q 0 c,
        frozenFineCellPairing a R b)
  let A : ℝ := frozenDescendantPairingColorScale M k' Q a
  have hD : D.Nonempty := by
    exact descendantsAtScale_nonempty Q hQ
  have hcolors : colors.Nonempty := by
    rcases hD with ⟨R, hR⟩
    exact ⟨cubeScaleColor 0 R, Finset.mem_image.mpr ⟨R, hR, rfl⟩⟩
  have hA : 0 < A := by
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
    have hK : 0 < streamIncrementLpNormScale M 2 (k' - 1) k' := by
      unfold streamIncrementLpNormScale
      exact Real.rpow_pos_of_pos
        (streamIncrementLpMassScale_pos M (by norm_num) (by omega)) _
    have hN : 0 < ((D.card : ℝ)) := by exact_mod_cast hD.card_pos
    have hparent : 0 < (D.card : ℝ) * cubeFrobeniusMassReg Q a :=
      mul_pos hN hmass
    dsimp [A, frozenDescendantPairingColorScale]
    exact mul_pos weightedSubgaussianConst_pos
      (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hd)) hK)
        (inv_pos.mpr hN)) (Real.sqrt_pos.2 hparent))
  have hY : ∀ c ∈ colors,
      Book.Ch04.IsBigO P (Book.Ch04.gammaSigma 2) (Y c) A := by
    intro c hc
    have hcTail := frozenColorPairing_isBigO M k' Q c a ha
    have hcLe := frozenColorPairingVarianceScale_le_parent M k' Q hQ c a ha
    exact hcTail.mono_scale hcLe
  have hYmeas : ∀ c ∈ colors, Measurable (Y c) := by
    intro c hc
    dsimp [Y]
    exact measurable_const.mul
      (Finset.measurable_sum _ fun R _ => measurable_frozenFineCellPairing a R)
  have hsum := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P) colors (by norm_num : (0 : ℝ) < 2) hcolors
    (fun _ _ => hA) hY hYmeas
  have hsum_eq :
      (fun b => ∑ c ∈ colors, Y c b) =
        fun b => (D.card : ℝ)⁻¹ *
          ∑ R ∈ D, frozenFineCellPairing a R b := by
    funext b
    rw [← Finset.mul_sum]
    congr 1
    calc
      ∑ c ∈ colors,
          ∑ R ∈ descendantsAtScaleScaleColorClass Q 0 c,
            frozenFineCellPairing a R b =
          ∑ R ∈ colors.biUnion
              (descendantsAtScaleScaleColorClass Q 0),
            frozenFineCellPairing a R b := by
        symm
        exact Finset.sum_biUnion (by
          intro c hc c' hc' hne
          exact disjoint_descendantsAtScaleScaleColorClass_of_ne Q 0 hne)
      _ = ∑ R ∈ D, frozenFineCellPairing a R b := by
        rw [show colors.biUnion (descendantsAtScaleScaleColorClass Q 0) = D by
          simpa only [colors, D] using
            descendantsAtScale_eq_biUnion_image_cubeScaleColor Q 0]
  rw [hsum_eq] at hsum
  simpa only [P, D, colors, A, Y, Finset.sum_const_zero,
    Finset.sum_const, nsmul_eq_mul, mul_assoc] using hsum

/-- If the frozen parent mass vanishes, the normalized descendant pairing is
almost surely zero and therefore has every nonnegative `Gamma_2` scale. -/
theorem frozenDescendantPairingAverage_isBigO_of_zero
    (M : ABKModel d) (k' : ℤ) (Q : TriadicCube d) (hQ : 0 ≤ Q.scale)
    (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (hmass : cubeFrobeniusMassReg Q a = 0) {A : ℝ} (hA : 0 ≤ A) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M (k' - 1) k')
      (Book.Ch04.gammaSigma 2)
      (fun b => ((descendantsAtScale Q 0).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q 0, frozenFineCellPairing a R b)
      A := by
  classical
  let P : Book.Ch04.RestrictionCoeffLaw d :=
    partitionStreamIncrementLaw M (k' - 1) k'
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  have hmassNonneg (R : TriadicCube d) : 0 ≤ cubeFrobeniusMassReg R a := by
    unfold cubeFrobeniusMassReg cubeAverage
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos R).le)
      (integral_nonneg fun x => matrixFrobeniusNormSq_nonneg _)
  have hsum : ∑ R ∈ D, cubeFrobeniusMassReg R a = 0 := by
    rw [show (∑ R ∈ D, cubeFrobeniusMassReg R a) =
        (D.card : ℝ) * cubeFrobeniusMassReg Q a by
      simpa only [D] using
        sum_cubeFrobeniusMassReg_descendantsAtScale Q hQ a ha,
      hmass, mul_zero]
  have hcellMass : ∀ R ∈ D, cubeFrobeniusMassReg R a = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg fun R _ => hmassNonneg R).mp hsum
  have hzero : (fun b => (D.card : ℝ)⁻¹ *
      ∑ R ∈ D, frozenFineCellPairing a R b) =ᵐ[P] 0 := by
    have hcells : ∀ R ∈ D, frozenFineCellPairing a R =ᵐ[P] 0 := by
      intro R hR
      exact frozenFineCellPairing_ae_zero_of_mass_zero
        M k' a ha R (hcellMass R hR)
    have hall : ∀ᵐ b ∂P, ∀ R, R ∈ D → frozenFineCellPairing a R b = 0 := by
      apply ae_all_iff.2
      intro R
      by_cases hR : R ∈ D
      · exact (hcells R hR).mono fun b hb _ => hb
      · exact Filter.Eventually.of_forall fun _ h => absurd h hR
    filter_upwards [hall] with b hb
    change (D.card : ℝ)⁻¹ *
      ∑ R ∈ D, frozenFineCellPairing a R b = (0 : ℝ)
    rw [Finset.sum_eq_zero fun R hR => hb R hR, mul_zero]
  have hbase : Book.Ch04.IsBigO P (Book.Ch04.gammaSigma 2)
      (fun _ : RegCoeffField d => (0 : ℝ)) A :=
    isBigO_gammaSigma_zero_fun hA
  exact (Book.Ch04.isBigO_congr_ae hzero).2 hbase

end

end Algsuperdiff.Section3.Provider.Stream
