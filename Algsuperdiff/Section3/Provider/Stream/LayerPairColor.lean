import Algsuperdiff.Section3.Provider.Stream.LayerPairCell
import Homogenization.Book.Ch04.Theorems.RestrictionIndependence

/-!
# Colored finer-shell concentration with a frozen coarser field

This internal module applies the restriction-unit-range coloring to the
cellwise pairings proved in `LayerPairCell`.  The local variance scales retain
the actual frozen cell masses, so summing them produces the required square
root of the parent mass rather than a worst-cell loss.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Orlicz

noncomputable section

variable {d : ℕ}

/-- The weighted variance scale for one finer-shell color class. -/
def frozenColorPairingVarianceScale (M : ABKModel d) (k' : ℤ)
    (Q : TriadicCube d) (c : ScaleColor d 0) (a : RegCoeffField d) : ℝ :=
  weightedSubgaussianConst *
    Real.sqrt
      (∑ R ∈ descendantsAtScaleScaleColorClass Q 0 c,
        (((descendantsAtScale Q 0).card : ℝ)⁻¹) ^ 2 *
          (16 * (((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a) *
            streamIncrementLpNormScale M 2 (k' - 1) k') ^ 2)))

/-- One color class of normalized finer cells has the exact weighted
sub-Gaussian scale. -/
theorem frozenColorPairing_isBigO
    (M : ABKModel d) (k' : ℤ) (Q : TriadicCube d) (c : ScaleColor d 0)
    (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M (k' - 1) k')
      (Book.Ch04.gammaSigma 2)
      (fun b => ((descendantsAtScale Q 0).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScaleScaleColorClass Q 0 c,
          frozenFineCellPairing a R b)
      (frozenColorPairingVarianceScale M k' Q c a) := by
  classical
  let P : Book.Ch04.RestrictionCoeffLaw d :=
    partitionStreamIncrementLaw M (k' - 1) k'
  let S : Finset (TriadicCube d) := descendantsAtScaleScaleColorClass Q 0 c
  let I : Type := {R : TriadicCube d // R ∈ S}
  let X : I → RegCoeffField d → ℝ := fun R => frozenFineCellPairing a R.1
  let A : I → ℝ := fun R =>
    (d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R.1 a) *
      streamIncrementLpNormScale M 2 (k' - 1) k'
  let w : I → ℝ := fun _ => ((descendantsAtScale Q 0).card : ℝ)⁻¹
  have hK : 0 < streamIncrementLpNormScale M 2 (k' - 1) k' := by
    unfold streamIncrementLpNormScale
    exact Real.rpow_pos_of_pos
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)) _
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have h_indep : iIndepFun X P := by
    exact Book.Ch04.iIndepFun_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
      (Q := Q) (k := 0) (c := c) (P := P)
      (partitionStreamIncrementLaw_unitRangeDependent M (k' - 1) k')
      (fun R => local_frozenFineCellPairing a R.1)
  have hX : ∀ R ∈ S.attach, AEMeasurable (X R) P := by
    intro R _
    exact (measurable_frozenFineCellPairing a R.1).aemeasurable
  have hA : ∀ R ∈ S.attach, 0 ≤ A R := by
    intro R _
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hK.le
  have hzero : ∀ R ∈ S.attach, A R = 0 → X R =ᵐ[P] 0 := by
    intro R _ hAR
    have hsqrt : Real.sqrt (cubeFrobeniusMassReg R.1 a) = 0 := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      rcases mul_eq_zero.mp hAR with hdc | hK0
      · rcases mul_eq_zero.mp hdc with hd0 | hs
        · exact absurd hd0 (ne_of_gt hdR)
        · exact hs
      · exact absurd hK0 (ne_of_gt hK)
    have hmassNonneg : 0 ≤ cubeFrobeniusMassReg R.1 a := by
      unfold cubeFrobeniusMassReg cubeAverage
      exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos R.1).le)
        (integral_nonneg fun x => matrixFrobeniusNormSq_nonneg _)
    have hmass : cubeFrobeniusMassReg R.1 a = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.mp hsqrt) hmassNonneg
    simpa only [P, X] using
      frozenFineCellPairing_ae_zero_of_mass_zero M k' a ha R.1 hmass
  have hcenter : ∀ R ∈ S.attach, ∫ b, X R b ∂P = 0 := by
    intro R _
    simpa only [P, X] using integral_frozenFineCellPairing_eq_zero M k' a ha R.1
  have htail : ∀ R ∈ S.attach,
      Book.Ch04.IsBigO P (Book.Ch04.gammaSigma 2) (X R) (A R) := by
    intro R _
    simpa only [P, X, A] using frozenFineCellPairing_isBigO M k' a ha R.1
  have hmain := weightedSum_of_gammaSigma_tails_nonneg
    (μ := P) (X := X) (A := A) (s := S.attach) w
    h_indep hX hA hzero hcenter htail
  have hfun : (fun b => ∑ R ∈ S.attach, w R * X R b) =
      fun b => ((descendantsAtScale Q 0).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScaleScaleColorClass Q 0 c,
          frozenFineCellPairing a R b := by
    funext b
    rw [← Finset.mul_sum]
    exact congrArg (((descendantsAtScale Q 0).card : ℝ)⁻¹ * ·)
      (by simpa only [S, I, X, w] using
        (Finset.sum_attach (s := S) (f := fun R => frozenFineCellPairing a R b)))
  rw [hfun] at hmain
  have hvar :
      (∑ R ∈ S.attach, (w R) ^ 2 * (16 * (A R) ^ 2)) =
        ∑ R ∈ S, (((descendantsAtScale Q 0).card : ℝ)⁻¹) ^ 2 *
          (16 * (((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a) *
            streamIncrementLpNormScale M 2 (k' - 1) k') ^ 2)) := by
    simpa only [I, A, w] using
      (Finset.sum_attach (s := S) (f := fun R =>
        (((descendantsAtScale Q 0).card : ℝ)⁻¹) ^ 2 *
          (16 * (((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a) *
            streamIncrementLpNormScale M 2 (k' - 1) k') ^ 2))))
  rw [hvar] at hmain
  simpa only [frozenColorPairingVarianceScale, P, S] using hmain

end

end Algsuperdiff.Section3.Provider.Stream
