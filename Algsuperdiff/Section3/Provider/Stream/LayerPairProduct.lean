import Algsuperdiff.Section3.Provider.Orlicz.FrozenProduct
import Algsuperdiff.Section3.Provider.Stream.LayerPairColoredAverage

/-!
# Product transport for a corrected large-gap shell pairing

This internal module combines the frozen-field colored estimate with the
independence of two distinct shell coordinates.  It yields the corrected
large-gap fixed-pair estimate; no premise from this construction is exposed in
a source-facing declaration.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Orlicz

noncomputable section

variable {d : ℕ}

/-- The measurable normalized pairing average used on the product carrier. -/
def frozenDescendantPairingAverage (Q : TriadicCube d)
    (p : RegCoeffField d × RegCoeffField d) : ℝ :=
  ((descendantsAtScale Q 0).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtScale Q 0,
      regFieldFrobeniusPairingRep (cubeSet R) p.1 p.2

theorem measurable_frozenDescendantPairingAverage (Q : TriadicCube d) :
    Measurable (frozenDescendantPairingAverage Q) := by
  unfold frozenDescendantPairingAverage
  exact measurable_const.mul
    (Finset.measurable_sum _ fun R _ =>
      measurable_regFieldFrobeniusPairingRep (cubeSet R))

/-- The deterministic coefficient multiplying the frozen upper-shell norm. -/
def layerPairCommonCoeff (M : ABKModel d) (k' l : ℤ) : ℝ :=
  let s := k' + (incrementPartitionShift d : ℤ)
  let Q := originCube d (l - s)
  Book.Ch04.gammaTriangleConst 2 *
    (((descendantsAtScale Q 0).image (cubeScaleColor 0)).card : ℝ) *
    weightedSubgaussianConst *
    (4 * (d : ℝ) * streamIncrementLpNormScale M 2 (k' - 1) k' *
      ((descendantsAtScale Q 0).card : ℝ)⁻¹)

/-- The deterministic scale before the product-tail constant. -/
def layerPairUpperDeterministicScale (M : ABKModel d) (k k' l : ℤ) : ℝ :=
  let s := k' + (incrementPartitionShift d : ℤ)
  let Q := originCube d (l - s)
  layerPairCommonCoeff M k' l *
    (Real.sqrt ((descendantsAtScale Q 0).card : ℝ) * (d : ℝ) *
      streamIncrementLpNormScale M 2 (k - 1) k)

/-- The random upper-shell scale used by the product-Fubini argument. -/
def layerPairFrozenUpperScale (M : ABKModel d) (k k' l : ℤ)
    (omega : ShellSeq d) : ℝ :=
  let s := k' + (incrementPartitionShift d : ℤ)
  let Q := originCube d (l - s)
  layerPairCommonCoeff M k' l *
    (Real.sqrt ((descendantsAtScale Q 0).card : ℝ) * (d : ℝ) *
      cubeStreamIncrementLpNorm 2 (originCube d l) (k - 1) k omega)

/-- The deterministic scale after multiplying the two `Gamma_2` envelopes. -/
def layerPairLargeGapScale (M : ABKModel d) (k k' l : ℤ) : ℝ :=
  Book.Ch04.gammaProductConst 2 2 *
    layerPairUpperDeterministicScale M k k' l

private theorem layerPairCommonCoeff_nonneg
    (M : ABKModel d) (k' l : ℤ) : 0 ≤ layerPairCommonCoeff M k' l := by
  let s : ℤ := k' + (incrementPartitionShift d : ℤ)
  let Q : TriadicCube d := originCube d (l - s)
  have hK : 0 < streamIncrementLpNormScale M 2 (k' - 1) k' := by
    unfold streamIncrementLpNormScale
    exact Real.rpow_pos_of_pos
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega)) _
  unfold layerPairCommonCoeff
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg IndependentSums.gammaTriangleConst_pos.le
        (Nat.cast_nonneg _)) weightedSubgaussianConst_pos.le)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hK.le)
      (inv_nonneg.mpr (Nat.cast_nonneg _)))

private theorem fineNormalizedSingleShellField_eq_coordinate (s k : ℤ) :
    fineNormalizedSingleShellField (d := d) s k =
      fun omega => smulReg ((3 : ℝ) ^ s) (zpow_ne_zero s (by norm_num))
        (Frozen.Assumptions.ShellField.forgetShell (omega k)) := by
  funext omega
  apply RegCoeffField.ext
  intro x
  ext i j
  have hIoc : Finset.Ioc (k - 1) k = {k} := by
    ext q
    simp
    omega
  rw [fineNormalizedSingleShellField, smulReg_apply,
    finiteShellIncrement_apply_entry, hIoc]
  simp

private theorem indepFun_fineNormalizedSingleShellField (M : ABKModel d)
    {s k k' : ℤ} (hne : k ≠ k') :
    IndepFun (fineNormalizedSingleShellField (d := d) s k)
      (fineNormalizedSingleShellField s k') M.P.toMeasure := by
  rw [fineNormalizedSingleShellField_eq_coordinate,
    fineNormalizedSingleShellField_eq_coordinate]
  let G : Frozen.Assumptions.ShellField d → RegCoeffField d := fun j =>
    smulReg ((3 : ℝ) ^ s) (zpow_ne_zero s (by norm_num))
      (Frozen.Assumptions.ShellField.forgetShell j)
  have hG : Measurable G := (measurable_smulReg _
    (zpow_ne_zero s (by norm_num))).comp
      Frozen.Assumptions.ShellField.measurable_forgetShell
  simpa only [G, Function.comp_apply] using
    (M.shellPrefix.independent.indepFun hne).comp hG hG

private theorem cubeFrobeniusMassReg_fineNormalized_eq
    (s k : ℤ) (Q : TriadicCube d) (omega : ShellSeq d) :
    cubeFrobeniusMassReg Q (fineNormalizedSingleShellField s k omega) =
      cubeFrobeniusMassReg (dilateCube s Q)
        (finiteShellIncrement omega (k - 1) k) := by
  rw [← regFieldFrobeniusMassRep_cubeSet_eq Q
      (fineNormalizedSingleShellField s k omega)
      (fun i j => continuous_fineNormalizedSingleShellField_entry s k omega i j)]
  exact regFieldFrobeniusMassRep_cubeSet_smulReg_eq s
    (zpow_ne_zero s (by norm_num)) rfl Q
    (finiteShellIncrement omega (k - 1) k)
    (fun i j => continuous_finiteShellIncrement_entry omega (k - 1) k i j)

private theorem layerPairFrozenUpperScale_nonneg
    (M : ABKModel d) (k k' l : ℤ) (omega : ShellSeq d) :
    0 ≤ layerPairFrozenUpperScale M k k' l omega := by
  unfold layerPairFrozenUpperScale
  exact mul_nonneg (layerPairCommonCoeff_nonneg M k' l)
    (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
      (cubeStreamIncrementLpNorm_nonneg (d := d) (p := 2)
        (by norm_num) _ _ _ _))

private theorem layerPairFrozenUpperScale_isBigO
    (M : ABKModel d) (k k' l : ℤ) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 2)
      (layerPairFrozenUpperScale M k k' l)
      (layerPairUpperDeterministicScale M k k' l) := by
  let s : ℤ := k' + (incrementPartitionShift d : ℤ)
  let Q : TriadicCube d := originCube d (l - s)
  let C : ℝ := layerPairCommonCoeff M k' l *
    (Real.sqrt ((descendantsAtScale Q 0).card : ℝ) * (d : ℝ))
  have hC : 0 ≤ C := by
    exact mul_nonneg (layerPairCommonCoeff_nonneg M k' l)
      (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
  have hraw := isBigOWith_gammaSigma_cubeStreamIncrementLpNorm
    M (p := 2) (by norm_num) (by omega : k - 1 < k) (originCube d l)
  have hwith := hraw.const_mul hC
  have hscale : C * streamIncrementLpNormScale M 2 (k - 1) k =
      layerPairUpperDeterministicScale M k k' l := by
    unfold layerPairUpperDeterministicScale
    dsimp only [s, Q, C]
    ring
  rw [← hscale]
  change IndependentSums.IsBigOWith M.P.toMeasure
    (IndependentSums.gammaSigma 2)
    (fun omega => |layerPairFrozenUpperScale M k k' l omega|) (C *
      streamIncrementLpNormScale M 2 (k - 1) k)
  have hfun : (fun omega => |layerPairFrozenUpperScale M k k' l omega|) =
      fun omega => C *
        cubeStreamIncrementLpNorm 2 (originCube d l) (k - 1) k omega := by
    funext omega
    rw [abs_of_nonneg (layerPairFrozenUpperScale_nonneg M k k' l omega)]
    unfold layerPairFrozenUpperScale
    dsimp only [s, Q, C]
    ring
  rw [hfun]
  exact hwith

private theorem frozenSlice_isBigO
    (M : ABKModel d) {k k' l : ℤ} (hgap :
      k' + (incrementPartitionShift d : ℤ) ≤ l)
    (omega : ShellSeq d) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M (k' - 1) k')
      (Book.Ch04.gammaSigma 2)
      (fun b => frozenDescendantPairingAverage
        (originCube d (l - (k' + (incrementPartitionShift d : ℤ))))
        (fineNormalizedSingleShellField
          (k' + (incrementPartitionShift d : ℤ)) k omega, b))
      (layerPairFrozenUpperScale M k k' l omega) := by
  let s : ℤ := k' + (incrementPartitionShift d : ℤ)
  let Q : TriadicCube d := originCube d (l - s)
  let a : RegCoeffField d := fineNormalizedSingleShellField s k omega
  have hQ : 0 ≤ Q.scale := by
    change 0 ≤ l - s
    exact sub_nonneg.mpr hgap
  have ha : ∀ i j, Continuous fun x : Vec d => a x i j := by
    intro i j
    exact continuous_fineNormalizedSingleShellField_entry s k omega i j
  have hN : 0 ≤ ((descendantsAtScale Q 0).card : ℝ) := by positivity
  have hmassNonneg : 0 ≤ cubeFrobeniusMassReg Q a := by
    unfold cubeFrobeniusMassReg cubeAverage
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos Q).le)
      (integral_nonneg fun x => matrixFrobeniusNormSq_nonneg _)
  have hscale :
      Book.Ch04.gammaTriangleConst 2 *
          (((descendantsAtScale Q 0).image (cubeScaleColor 0)).card : ℝ) *
          frozenDescendantPairingColorScale M k' Q a ≤
        layerPairFrozenUpperScale M k k' l omega := by
    have hmassEq := cubeFrobeniusMassReg_fineNormalized_eq s k Q omega
    have hdilate : dilateCube s Q = originCube d l := by
      dsimp only [Q]
      rw [dilateCube_originCube]
      congr
      dsimp [s]
      ring
    have hroot := sqrt_cubeFrobeniusMassReg_finiteShellIncrement_le
      (originCube d l) (k - 1) k omega
    rw [← hdilate, ← hmassEq] at hroot
    let C : ℝ := layerPairCommonCoeff M k' l
    have hC : 0 ≤ C := by
      exact layerPairCommonCoeff_nonneg M k' l
    have hleft : Book.Ch04.gammaTriangleConst 2 *
          (((descendantsAtScale Q 0).image (cubeScaleColor 0)).card : ℝ) *
          frozenDescendantPairingColorScale M k' Q a =
        C * Real.sqrt (((descendantsAtScale Q 0).card : ℝ) *
          cubeFrobeniusMassReg Q a) := by
      unfold frozenDescendantPairingColorScale
      dsimp only [C, layerPairCommonCoeff]
      ring
    have hright : layerPairFrozenUpperScale M k k' l omega =
        C * (Real.sqrt ((descendantsAtScale Q 0).card : ℝ) * (d : ℝ) *
          cubeStreamIncrementLpNorm 2 (originCube d l) (k - 1) k omega) := by
      unfold layerPairFrozenUpperScale
      dsimp only [C, Q, s]
    have hroot' : Real.sqrt (cubeFrobeniusMassReg Q a) ≤
        (d : ℝ) * cubeStreamIncrementLpNorm 2
          (originCube d l) (k - 1) k omega := by
      simpa only [a, hdilate] using hroot
    rw [hleft, hright, Real.sqrt_mul hN]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hroot'
          (Real.sqrt_nonneg ((descendantsAtScale Q 0).card : ℝ)))) hC
  by_cases hm : cubeFrobeniusMassReg Q a = 0
  · have hzero := frozenDescendantPairingAverage_isBigO_of_zero
      M k' Q hQ a ha hm (layerPairFrozenUpperScale_nonneg M k k' l omega)
    simpa only [frozenDescendantPairingAverage, Q, s, a] using hzero
  · have hpos : 0 < cubeFrobeniusMassReg Q a :=
      lt_of_le_of_ne hmassNonneg (Ne.symm hm)
    have hraw := frozenDescendantPairingAverage_isBigO_of_pos
      M k' Q hQ a ha hpos
    exact (by
      simpa only [frozenDescendantPairingAverage, Q, s, a] using
        hraw.mono_scale hscale)

/-- Corrected large-gap fixed-pair concentration before deterministic scale
simplification.  The descendant-count gain is present in
`layerPairLargeGapScale`. -/
theorem cubeFrobeniusPairingReg_singleShell_isBigO_largeGap
    (M : ABKModel d) {k k' l : ℤ} (hne : k ≠ k')
    (hgap : k' + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega => cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega (k - 1) k)
        (finiteShellIncrement omega (k' - 1) k'))
      (layerPairLargeGapScale M k k' l) := by
  let s : ℤ := k' + (incrementPartitionShift d : ℤ)
  let Q : TriadicCube d := originCube d (l - s)
  let Fu : ShellSeq d → RegCoeffField d := fineNormalizedSingleShellField s k
  let Fl : ShellSeq d → RegCoeffField d := fineNormalizedSingleShellField s k'
  let lowerLaw : Measure (RegCoeffField d) :=
    partitionStreamIncrementLaw M (k' - 1) k'
  let F : ShellSeq d × RegCoeffField d → ℝ := fun p =>
    frozenDescendantPairingAverage Q (Fu p.1, p.2)
  let A : ShellSeq d → ℝ := layerPairFrozenUpperScale M k k' l
  have hFu : Measurable Fu := measurable_fineNormalizedSingleShellField s k
  have hFl : Measurable Fl := measurable_fineNormalizedSingleShellField s k'
  have hF : Measurable F := by
    exact (measurable_frozenDescendantPairingAverage Q).comp
      ((hFu.comp measurable_fst).prodMk measurable_snd)
  have hAmeas : Measurable A := by
    have hnorm := measurable_cubeStreamIncrementLpNorm_local
      (d := d) (by norm_num : (0 : ℝ) < 2)
      (originCube d l) (k - 1) k
    have heq : A = fun omega =>
        (layerPairCommonCoeff M k' l *
          (Real.sqrt
            ((descendantsAtScale
              (originCube d (l - (k' + (incrementPartitionShift d : ℤ)))) 0).card : ℝ) *
            (d : ℝ))) *
          cubeStreamIncrementLpNorm 2 (originCube d l) (k - 1) k omega := by
      funext omega
      unfold A layerPairFrozenUpperScale
      ring
    rw [heq]
    exact measurable_const.mul hnorm
  have hprod := isBigO_gammaSigma_frozen_product
    (P := M.P.toMeasure) (Q := lowerLaw)
    (F := F) (A := A)
    (B := layerPairUpperDeterministicScale M k k' l)
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    hAmeas hF (layerPairFrozenUpperScale_nonneg M k k' l)
    (layerPairFrozenUpperScale_isBigO M k k' l)
    (Filter.Eventually.of_forall fun omega => by
      simpa only [F, A, Q, Fu, lowerLaw] using
        frozenSlice_isBigO M hgap omega)
  have hprod' : Book.Ch04.IsBigO (M.P.toMeasure.prod lowerLaw)
      (Book.Ch04.gammaSigma 1) F (layerPairLargeGapScale M k k' l) := by
    simpa only [show (2 : ℝ) * 2 / (2 + 2) = 1 by norm_num,
      layerPairLargeGapScale] using hprod
  have hcarrier := isBigO_map_of_comp
    (μ := M.P.toMeasure.prod lowerLaw)
    (f := fun p : ShellSeq d × RegCoeffField d => (Fu p.1, p.2))
    (X := frozenDescendantPairingAverage Q)
    ((hFu.comp measurable_fst).prodMk measurable_snd)
    (measurable_frozenDescendantPairingAverage Q) hprod'
  have hlower : lowerLaw = Measure.map Fl M.P.toMeasure := by
    dsimp only [lowerLaw]
    rw [partitionStreamIncrementLaw_eq_map]
    congr
  have hmapProd : Measure.map
      (fun p : ShellSeq d × RegCoeffField d => (Fu p.1, p.2))
      (M.P.toMeasure.prod lowerLaw) =
      (Measure.map Fu M.P.toMeasure).prod lowerLaw := by
    rw [show (fun p : ShellSeq d × RegCoeffField d => (Fu p.1, p.2)) =
        Prod.map Fu id by rfl,
      ← Measure.map_prod_map M.P.toMeasure lowerLaw hFu measurable_id,
      Measure.map_id]
  rw [hmapProd, hlower] at hcarrier
  have hindep := indepFun_fineNormalizedSingleShellField M (s := s) hne
  have hpairLaw :=
    (indepFun_iff_map_prod_eq_prod_map_map hFu.aemeasurable hFl.aemeasurable).mp hindep
  rw [← hpairLaw] at hcarrier
  have hpull := isBigO_comp_of_map
    (μ := M.P.toMeasure)
    (f := fun omega : ShellSeq d => (Fu omega, Fl omega))
    (X := frozenDescendantPairingAverage Q)
    (hFu.prodMk hFl) (measurable_frozenDescendantPairingAverage Q) hcarrier
  have hfun : (fun omega => frozenDescendantPairingAverage Q
      (Fu omega, Fl omega)) = fun omega =>
      cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega (k - 1) k)
        (finiteShellIncrement omega (k' - 1) k') := by
    funext omega
    rw [frozenDescendantPairingAverage,
      descendantAverage_regFieldFrobeniusPairingRep Q (by
        change 0 ≤ l - s
        exact sub_nonneg.mpr hgap) (Fu omega) (Fl omega)
        (fun i j => continuous_fineNormalizedSingleShellField_entry s k omega i j)
        (fun i j => continuous_fineNormalizedSingleShellField_entry s k' omega i j)]
    simpa only [Fu, Fl, Q, s] using
      regFieldFrobeniusPairingRep_fineNormalized_eq s l k k' omega
  rw [hfun] at hpull
  exact hpull

end

end Algsuperdiff.Section3.Provider.Stream
