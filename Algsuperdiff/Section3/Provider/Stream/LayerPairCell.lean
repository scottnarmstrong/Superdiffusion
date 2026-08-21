import Algsuperdiff.Section3.Provider.Orlicz.WeightedSubgaussian
import Algsuperdiff.Section3.Provider.Stream.FrobeniusPairingRepresentative
import Algsuperdiff.Section3.Provider.Stream.LayerDiagonalAllGap
import Algsuperdiff.Section3.Provider.Stream.IncrementTranslation
import Algsuperdiff.Section3.Cutoff.Symmetry

/-!
# One-cell estimates for a corrected two-shell pairing

This internal module freezes the coarser shell and estimates its pairing with
one cell of the finer shell.  It makes no source-node status claim.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Filter MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- A single shell, spatially normalized at an arbitrary physical scale. -/
def fineNormalizedSingleShellField (s k : ℤ) (omega : ShellSeq d) :
    RegCoeffField d :=
  smulReg ((3 : ℝ) ^ s) (zpow_ne_zero s (by norm_num))
    (finiteShellIncrement omega (k - 1) k)

theorem measurable_fineNormalizedSingleShellField (s k : ℤ) :
    Measurable (fineNormalizedSingleShellField (d := d) s k) :=
  (measurable_smulReg _ _).comp (measurable_finiteShellIncrement (k - 1) k)

theorem continuous_fineNormalizedSingleShellField_entry (s k : ℤ)
    (omega : ShellSeq d) (i j : Fin d) :
    Continuous (fun x : Vec d =>
      fineNormalizedSingleShellField s k omega x i j) := by
  exact (continuous_finiteShellIncrement_entry omega (k - 1) k i j).comp
    (continuous_const_smul ((3 : ℝ) ^ s))

/-- At the finer shell's normalization scale this is exactly the map defining its
proved restriction law. -/
theorem fineNormalizedSingleShellField_eq_partitionField (k : ℤ)
    (omega : ShellSeq d) :
    fineNormalizedSingleShellField
        (k + (incrementPartitionShift d : ℤ)) k omega =
      smulReg (incrementPartitionScale d k)
        (incrementPartitionScale_ne_zero d k)
        (finiteShellIncrement omega (k - 1) k) := by
  apply RegCoeffField.ext
  intro x
  rfl

/-- The normalized representative is the honest physical pairing. -/
theorem regFieldFrobeniusPairingRep_fineNormalized_eq
    (s l k k' : ℤ) (omega : ShellSeq d) :
    regFieldFrobeniusPairingRep
        (cubeSet (originCube d (l - s)))
        (fineNormalizedSingleShellField s k omega)
        (fineNormalizedSingleShellField s k' omega) =
      cubeFrobeniusPairingReg (originCube d l)
        (finiteShellIncrement omega (k - 1) k)
        (finiteShellIncrement omega (k' - 1) k') := by
  rw [fineNormalizedSingleShellField, fineNormalizedSingleShellField,
    regFieldFrobeniusPairingRep_cubeSet_smulReg_eq s
      (zpow_ne_zero s (by norm_num)) rfl]
  · rw [dilateCube_originCube]
    congr 2
    ring
  · exact fun i j => continuous_finiteShellIncrement_entry omega (k - 1) k i j
  · exact fun i j => continuous_finiteShellIncrement_entry omega (k' - 1) k' i j

/-- Frobenius mass on a cube is bounded by `d²` times the operator-norm
square mass. -/
theorem cubeFrobeniusMassReg_finiteShellIncrement_le
    (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) :
    cubeFrobeniusMassReg Q (finiteShellIncrement omega n m) ≤
      (d : ℝ) ^ 2 *
        cubeAverage Q (streamIncrementLpDensity 2 n m omega) := by
  unfold cubeFrobeniusMassReg cubeAverage
  have hvol : 0 ≤ (cubeVolume Q)⁻¹ := inv_nonneg.mpr (cubeVolume_pos Q).le
  have hleft : IntegrableOn
      (fun x => matrixFrobeniusNormSq (finiteShellIncrement omega n m x))
      (cubeSet Q) volume :=
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_finiteShellIncrement_entry omega n m i j).pow 2).continuousOn
      |>.integrableOn_compact
        (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
          (cubeSet_subset_closedBall Q)
  have hright : IntegrableOn
      (fun x => (d : ℝ) ^ 2 * streamIncrementLpDensity 2 n m omega x)
      (cubeSet Q) volume :=
    (integrableOn_cubeSet_streamIncrementLpDensity (by norm_num) Q n m omega).const_mul _
  have hint :
      ∫ x in cubeSet Q, matrixFrobeniusNormSq (finiteShellIncrement omega n m x)
          ∂volume ≤
        ∫ x in cubeSet Q,
          (d : ℝ) ^ 2 * streamIncrementLpDensity 2 n m omega x ∂volume := by
    refine setIntegral_mono_on hleft hright (measurableSet_cubeSet Q) ?_
    intro x _
    simpa only [streamIncrementLpDensity, Real.rpow_two] using
      (matrixFrobeniusNormSq_le_of_abs_entry_le fun i j =>
        Book.Ch02.abs_entry_le_matrixOperatorNorm
          (finiteShellIncrement omega n m x) i j)
  calc
    (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet Q, matrixFrobeniusNormSq (finiteShellIncrement omega n m x)
          ∂volume ≤
      (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet Q,
          (d : ℝ) ^ 2 * streamIncrementLpDensity 2 n m omega x ∂volume :=
      mul_le_mul_of_nonneg_left hint hvol
    _ = (d : ℝ) ^ 2 *
        ((cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, streamIncrementLpDensity 2 n m omega x ∂volume) := by
      rw [integral_const_mul]
      ring

/-- Square-root form of the preceding deterministic comparison. -/
theorem sqrt_cubeFrobeniusMassReg_finiteShellIncrement_le
    (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) :
    Real.sqrt (cubeFrobeniusMassReg Q (finiteShellIncrement omega n m)) ≤
      (d : ℝ) * cubeStreamIncrementLpNorm 2 Q n m omega := by
  have hmass := cubeFrobeniusMassReg_finiteShellIncrement_le Q n m omega
  have havg : 0 ≤ cubeAverage Q (streamIncrementLpDensity 2 n m omega) := by
    unfold cubeAverage
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos Q).le)
      (integral_nonneg fun x => Real.rpow_nonneg
        (Book.Ch02.matrixOperatorNorm_nonneg _) _)
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hnorm : cubeStreamIncrementLpNorm 2 Q n m omega =
      Real.sqrt (cubeAverage Q (streamIncrementLpDensity 2 n m omega)) := by
    unfold cubeStreamIncrementLpNorm
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
      ← Real.sqrt_eq_rpow]
  rw [hnorm]
  calc
    Real.sqrt (cubeFrobeniusMassReg Q (finiteShellIncrement omega n m)) ≤
        Real.sqrt ((d : ℝ) ^ 2 *
          cubeAverage Q (streamIncrementLpDensity 2 n m omega)) :=
      Real.sqrt_le_sqrt hmass
    _ = (d : ℝ) *
        Real.sqrt (cubeAverage Q (streamIncrementLpDensity 2 n m omega)) := by
      rw [Real.sqrt_mul (sq_nonneg (d : ℝ)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hd]

/-- Measurability of the arbitrary-cube increment norm used in the local
integrability argument. -/
theorem measurable_cubeStreamIncrementLpNorm_local {p : ℝ} (hp : 0 < p)
    (Q : TriadicCube d) (n m : ℤ) :
    Measurable (cubeStreamIncrementLpNorm p Q n m) := by
  have hswap : (fun q : ShellSeq d × Vec d =>
      streamIncrementLpDensity p n m q.1 q.2) =
      Function.uncurry (fun (x : Vec d) (w : ShellSeq d) =>
        streamIncrementLpDensity p n m w x) ∘ Prod.swap := rfl
  have hjoint : Measurable fun q : ShellSeq d × Vec d =>
      streamIncrementLpDensity p n m q.1 q.2 := by
    rw [hswap]
    exact (measurable_uncurry_streamIncrementLpDensity hp n m).comp measurable_swap
  have hSM := MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (cubeSet Q))
    (f := fun (w : ShellSeq d) (x : Vec d) =>
      streamIncrementLpDensity p n m w x) hjoint.stronglyMeasurable
  have hmass : Measurable (fun omega : ShellSeq d =>
      cubeAverage Q (streamIncrementLpDensity p n m omega)) := by
    unfold cubeAverage
    exact measurable_const.mul hSM.measurable
  exact hmass.pow_const _

/-- The local pairing observable with the coarser normalized field frozen. -/
def frozenFineCellPairing (a : RegCoeffField d) (R : TriadicCube d)
    (b : RegCoeffField d) : ℝ :=
  regFieldFrobeniusPairingRep (cubeSet R) a b

theorem measurable_frozenFineCellPairing (a : RegCoeffField d)
    (R : TriadicCube d) : Measurable (frozenFineCellPairing a R) :=
  measurable_regFieldFrobeniusPairingRep_comp (cubeSet R)
    measurable_const measurable_id

theorem local_frozenFineCellPairing (a : RegCoeffField d)
    (R : TriadicCube d) :
    Book.Ch04.IsRestrictionLocalRandomVariable (cubeSet R)
      (measurableSet_cubeSet R) (frozenFineCellPairing a R) :=
  isLocalRandomVariable_regFieldFrobeniusPairingRep_const
    (measurableSet_cubeSet R) a

/-- Deterministic domination of a normalized one-cell pairing by the finer
shell's physical cube norm. -/
theorem abs_frozenFineCellPairing_fineNormalized_le
    (k' : ℤ) (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (R : TriadicCube d) (omega : ShellSeq d) :
    |frozenFineCellPairing a R
        (fineNormalizedSingleShellField
          (k' + (incrementPartitionShift d : ℤ)) k' omega)| ≤
      ((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a)) *
        cubeStreamIncrementLpNorm 2
          (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
          (k' - 1) k' omega := by
  let F : ShellSeq d → RegCoeffField d :=
    fineNormalizedSingleShellField
      (k' + (incrementPartitionShift d : ℤ)) k'
  have hFcont : ∀ i j, Continuous fun x : Vec d => F omega x i j := by
    intro i j
    exact continuous_fineNormalizedSingleShellField_entry _ _ omega i j
  have heq := regFieldFrobeniusPairingRep_cubeSet_eq R a (F omega) ha hFcont
  have hlowerEq : cubeFrobeniusMassReg R (F omega) =
      cubeFrobeniusMassReg
        (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
        (finiteShellIncrement omega (k' - 1) k') := by
    rw [← regFieldFrobeniusMassRep_cubeSet_eq R (F omega) hFcont]
    exact regFieldFrobeniusMassRep_cubeSet_smulReg_eq
      (k' + (incrementPartitionShift d : ℤ))
      (incrementPartitionScale_ne_zero d k') rfl R
      (finiteShellIncrement omega (k' - 1) k')
      (fun i j => continuous_finiteShellIncrement_entry omega (k' - 1) k' i j)
  have hCS := abs_cubeFrobeniusPairingReg_le R a (F omega) ha hFcont
  have hlower := sqrt_cubeFrobeniusMassReg_finiteShellIncrement_le
    (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
    (k' - 1) k' omega
  rw [frozenFineCellPairing, heq]
  calc
    |cubeFrobeniusPairingReg R a (F omega)| ≤
        Real.sqrt (cubeFrobeniusMassReg R a) *
          Real.sqrt (cubeFrobeniusMassReg R (F omega)) := hCS
    _ ≤ Real.sqrt (cubeFrobeniusMassReg R a) *
        ((d : ℝ) * cubeStreamIncrementLpNorm 2
          (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
          (k' - 1) k' omega) := by
      rw [hlowerEq]
      gcongr
    _ = ((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a)) *
        cubeStreamIncrementLpNorm 2
          (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
          (k' - 1) k' omega := by ring

/-- One frozen cell has a `Gamma_2` tail at the finer-shell norm scale times
the square root of the frozen local Frobenius mass. -/
theorem frozenFineCellPairing_isBigO
    (M : ABKModel d) (k' : ℤ) (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (R : TriadicCube d) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M (k' - 1) k')
      (Book.Ch04.gammaSigma 2) (frozenFineCellPairing a R)
      ((d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a) *
        streamIncrementLpNormScale M 2 (k' - 1) k') := by
  let F : ShellSeq d → RegCoeffField d :=
    fineNormalizedSingleShellField
      (k' + (incrementPartitionShift d : ℤ)) k'
  let c : ℝ := (d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a)
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hraw := isBigOWith_gammaSigma_cubeStreamIncrementLpNorm
    M (p := 2) (by norm_num) (by omega : k' - 1 < k')
      (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
  have hcomp : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega =>
        |frozenFineCellPairing a R (F omega)|)
      (c * streamIncrementLpNormScale M 2 (k' - 1) k') := by
    refine (hraw.const_mul hc).of_le fun omega => ?_
    simpa only [F, c] using
      abs_frozenFineCellPairing_fineNormalized_le k' a ha R omega
  have hmap : IndependentSums.IsBigO
      (Measure.map F M.P.toMeasure) (IndependentSums.gammaSigma 2)
      (frozenFineCellPairing a R)
      (c * streamIncrementLpNormScale M 2 (k' - 1) k') := by
    exact isBigOWith_map_of_isBigOWith_comp M.P.toMeasure
      (measurable_fineNormalizedSingleShellField _ _)
      (continuous_abs.measurable.comp (measurable_frozenFineCellPairing a R)) hcomp
  rw [partitionStreamIncrementLaw_eq_map]
  simpa only [F, c, fineNormalizedSingleShellField_eq_partitionField] using hmap

/-- Negating the shell sequence negates every normalized single shell. -/
theorem fineNormalizedSingleShellField_negateSequence (s k : ℤ)
    (omega : ShellSeq d) :
    fineNormalizedSingleShellField s k
        (Frozen.Assumptions.ShellField.negateSequence omega) =
      Algsuperdiff.Probability.negReg
        (fineNormalizedSingleShellField s k omega) := by
  ext x i j
  simp only [fineNormalizedSingleShellField, smulReg_apply,
    finiteShellIncrement_apply_entry,
    Frozen.Assumptions.ShellField.negateSequence_apply,
    Frozen.Assumptions.ShellField.negate_apply, Matrix.neg_apply,
    Algsuperdiff.Probability.negReg_apply, ← Finset.sum_neg_distrib]

private theorem cubeFrobeniusPairingReg_neg_right
    (Q : TriadicCube d) (a b : RegCoeffField d) :
    cubeFrobeniusPairingReg Q a (Algsuperdiff.Probability.negReg b) =
      -cubeFrobeniusPairingReg Q a b := by
  unfold cubeFrobeniusPairingReg cubeAverage
  have hfun : (fun x : Vec d => ∑ i, ∑ j,
      a x i j * Algsuperdiff.Probability.negReg b x i j) =
      fun x => -(∑ i, ∑ j, a x i j * b x i j) := by
    funext x
    simp only [Algsuperdiff.Probability.negReg_apply, Matrix.neg_apply,
      mul_neg, Finset.sum_neg_distrib]
  have hIntNeg :
      ∫ x in cubeSet Q, -(∑ i, ∑ j, a x i j * b x i j) ∂volume =
        -∫ x in cubeSet Q, ∑ i, ∑ j, a x i j * b x i j ∂volume :=
    integral_neg _
  rw [hfun, hIntNeg]
  ring

/-- The fine-cell pairing has zero mean under the normalized finer-shell law.
The proof uses the exact J3 whole-sequence negation symmetry; centering is not
added as a hypothesis. -/
theorem integral_frozenFineCellPairing_eq_zero
    (M : ABKModel d) (k' : ℤ) (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (R : TriadicCube d) :
    ∫ b, frozenFineCellPairing a R b
        ∂(partitionStreamIncrementLaw M (k' - 1) k') = 0 := by
  let F : ShellSeq d → RegCoeffField d :=
    fineNormalizedSingleShellField
      (k' + (incrementPartitionShift d : ℤ)) k'
  let Y : ShellSeq d → ℝ := fun omega => frozenFineCellPairing a R (F omega)
  let c : ℝ := (d : ℝ) * Real.sqrt (cubeFrobeniusMassReg R a)
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hnorm := isBigOWith_gammaSigma_cubeStreamIncrementLpNorm
    M (p := 2) (by norm_num) (by omega : k' - 1 < k')
      (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
  have hnormInt : Integrable
      (cubeStreamIncrementLpNorm 2
        (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
        (k' - 1) k') M.P.toMeasure := by
    simpa only [Real.rpow_one] using
      (IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
        (Y := cubeStreamIncrementLpNorm 2
          (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
          (k' - 1) k')
        (K := streamIncrementLpNormScale M 2 (k' - 1) k')
        (σ := 2) (p := 1) (by norm_num)
        (by
          unfold streamIncrementLpNormScale
          exact Real.rpow_pos_of_pos
            (streamIncrementLpMassScale_pos M (by norm_num) (by omega)) _)
        (by norm_num)
        (cubeStreamIncrementLpNorm_nonneg (by norm_num) _ _ _)
        (measurable_cubeStreamIncrementLpNorm_local (by norm_num) _ _ _).aemeasurable
        hnorm)
  have hYmeas : Measurable Y :=
    (measurable_frozenFineCellPairing a R).comp
      (measurable_fineNormalizedSingleShellField _ _)
  have hYint : Integrable Y M.P.toMeasure := by
    refine (hnormInt.const_mul c).mono' hYmeas.aestronglyMeasurable ?_
    filter_upwards with omega
    have hcube0 : 0 ≤ cubeStreamIncrementLpNorm 2
        (dilateCube (k' + (incrementPartitionShift d : ℤ)) R)
        (k' - 1) k' omega :=
      cubeStreamIncrementLpNorm_nonneg (d := d) (p := 2) (by norm_num) _ _ _ _
    simpa only [Real.norm_eq_abs, Y, F, c,
      abs_of_nonneg (mul_nonneg hc hcube0)] using
      abs_frozenFineCellPairing_fineNormalized_le k' a ha R omega
  have hodd : ∀ omega,
      Y (Frozen.Assumptions.ShellField.negateSequence omega) = -Y omega := by
    intro omega
    have hFcont : ∀ i j, Continuous fun x : Vec d =>
        fineNormalizedSingleShellField
          (k' + (incrementPartitionShift d : ℤ)) k' omega x i j :=
      fun i j => continuous_fineNormalizedSingleShellField_entry _ _ omega i j
    have hnegCont : ∀ i j, Continuous fun x : Vec d =>
        Algsuperdiff.Probability.negReg
          (fineNormalizedSingleShellField
            (k' + (incrementPartitionShift d : ℤ)) k' omega) x i j := by
      intro i j
      simpa only [Algsuperdiff.Probability.negReg_apply, Matrix.neg_apply] using
        (hFcont i j).neg
    dsimp only [Y]
    change frozenFineCellPairing a R
        (fineNormalizedSingleShellField
          (k' + (incrementPartitionShift d : ℤ)) k'
          (Frozen.Assumptions.ShellField.negateSequence omega)) =
      -frozenFineCellPairing a R
        (fineNormalizedSingleShellField
          (k' + (incrementPartitionShift d : ℤ)) k' omega)
    rw [fineNormalizedSingleShellField_negateSequence]
    unfold frozenFineCellPairing
    rw [regFieldFrobeniusPairingRep_cubeSet_eq R a
        (Algsuperdiff.Probability.negReg
          (fineNormalizedSingleShellField
            (k' + (incrementPartitionShift d : ℤ)) k' omega)) ha hnegCont,
      regFieldFrobeniusPairingRep_cubeSet_eq R a
        (fineNormalizedSingleShellField
          (k' + (incrementPartitionShift d : ℤ)) k' omega) ha hFcont,
      cubeFrobeniusPairingReg_neg_right R a
        (fineNormalizedSingleShellField
          (k' + (incrementPartitionShift d : ℤ)) k' omega)]
  have hJ3 := congrArg ProbabilityMeasure.toMeasure M.J3.negation
  change Measure.map Frozen.Assumptions.ShellField.negateSequence M.P.toMeasure =
    M.P.toMeasure at hJ3
  have hsymm : ∫ omega, Y (Frozen.Assumptions.ShellField.negateSequence omega)
      ∂M.P.toMeasure = ∫ omega, Y omega ∂M.P.toMeasure := by
    calc
      ∫ omega, Y (Frozen.Assumptions.ShellField.negateSequence omega)
          ∂M.P.toMeasure =
        ∫ omega, Y omega ∂(Measure.map
          Frozen.Assumptions.ShellField.negateSequence M.P.toMeasure) := by
            exact (integral_map
              Frozen.Assumptions.ShellField.measurable_negateSequence.aemeasurable
              hYmeas.aestronglyMeasurable).symm
      _ = ∫ omega, Y omega ∂M.P.toMeasure := by rw [hJ3]
  have hnegint : ∫ omega,
      Y (Frozen.Assumptions.ShellField.negateSequence omega) ∂M.P.toMeasure =
      -∫ omega, Y omega ∂M.P.toMeasure := by
    calc
      ∫ omega, Y (Frozen.Assumptions.ShellField.negateSequence omega)
          ∂M.P.toMeasure = ∫ omega, -Y omega ∂M.P.toMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hodd)
      _ = -∫ omega, Y omega ∂M.P.toMeasure := integral_neg Y
  have hYzero : ∫ omega, Y omega ∂M.P.toMeasure = 0 := by linarith
  rw [partitionStreamIncrementLaw_eq_map,
    integral_map (measurable_partitionIncrementField (d := d) (k' - 1) k').aemeasurable
      (measurable_frozenFineCellPairing a R).aestronglyMeasurable]
  simpa only [Y, F, fineNormalizedSingleShellField_eq_partitionField] using hYzero

/-- If the frozen field has zero mass on a cell, its pairing with the finer
shell is almost surely zero under the normalized finer-shell law. -/
theorem frozenFineCellPairing_ae_zero_of_mass_zero
    (M : ABKModel d) (k' : ℤ) (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (R : TriadicCube d) (hzero : cubeFrobeniusMassReg R a = 0) :
    frozenFineCellPairing a R =ᵐ[partitionStreamIncrementLaw M (k' - 1) k'] 0 := by
  let F : ShellSeq d → RegCoeffField d :=
    fineNormalizedSingleShellField
      (k' + (incrementPartitionShift d : ℤ)) k'
  rw [partitionStreamIncrementLaw_eq_map]
  have hset : MeasurableSet {b : RegCoeffField d |
      frozenFineCellPairing a R b = 0} := by
    change MeasurableSet (frozenFineCellPairing a R ⁻¹' ({0} : Set ℝ))
    exact (measurable_frozenFineCellPairing a R) (measurableSet_singleton 0)
  apply (ae_map_iff (measurable_partitionIncrementField (d := d) (k' - 1) k').aemeasurable
    hset).2
  filter_upwards with omega
  have hle := abs_frozenFineCellPairing_fineNormalized_le k' a ha R omega
  rw [hzero, Real.sqrt_zero, mul_zero, zero_mul] at hle
  have : frozenFineCellPairing a R (F omega) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  simpa only [F, fineNormalizedSingleShellField_eq_partitionField] using this

end

end Algsuperdiff.Section3.Provider.Stream
