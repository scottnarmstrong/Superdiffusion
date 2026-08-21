import Algsuperdiff.Section3.Provider.Stream.CutoffL2Expectation
import Algsuperdiff.Section3.Provider.Stream.FrobeniusMassRepresentative
import Algsuperdiff.Section3.Provider.Stream.IncrementLpLarge
import Algsuperdiff.Section3.Provider.Stream.IncrementLpSquared

/-!
# Finite-range concentration of one shell's diagonal Frobenius mass

This is the first probabilistic node missing from the corrected proof of
ABK26's `e.km.kn.L2.bound`.  A single shell's Frobenius mass is decomposed into
its finitely many squared scalar entries.  Each entry uses the local measurable
representative from `FrobeniusMassRepresentative`, and CoarseGraining's
restriction-law partition theorem supplies the square-root descendant gain.

The module is provider infrastructure.  It neither declares nor assigns status
to the source node `e.km.kn.L2.bound`; the off-diagonal two-scale pairing and
the final all-gap assembly remain separate proof steps.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Filter MeasureTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The literal volume-normalized square of one scalar entry of a finite stream
increment on an origin cube. -/
def cubeAverageFiniteShellEntrySq (l n m : ℤ) (i j : Fin d)
    (omega : ShellSeq d) : ℝ :=
  cubeAverage (originCube d l)
    (fun x => (finiteShellIncrement omega n m x i j) ^ 2)

private theorem integrableOn_finiteShellEntrySq (l n m : ℤ) (i j : Fin d)
    (omega : ShellSeq d) :
    IntegrableOn (fun x => (finiteShellIncrement omega n m x i j) ^ 2)
      (cubeSet (originCube d l)) volume := by
  have hcont : Continuous fun x : Vec d => finiteShellIncrement omega n m x i j :=
    continuous_finiteShellIncrement_entry omega n m i j
  exact (hcont.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter (originCube d l))
        (cubeRadius (originCube d l))) |>.mono_set
        (cubeSet_subset_closedBall (originCube d l))

/-- Partition a squared entry average at any finer triadic scale. -/
theorem cubeAverageFiniteShellEntrySq_eq_descendantAverage_of_scale
    {l s : ℤ} (hsl : s ≤ l) (n m : ℤ) (i j : Fin d) (omega : ShellSeq d) :
    cubeAverageFiniteShellEntrySq l n m i j omega =
      ((descendantsAtScale (originCube d l) s).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d l) s,
          cubeAverage R (fun x => (finiteShellIncrement omega n m x i j) ^ 2) := by
  have hscale : descendantsAtScale (originCube d l) s =
      descendantsAtDepth (originCube d l) (Int.toNat (l - s)) :=
    descendantsAtScale_eq_descendantsAtDepth (originCube d l) hsl
  rw [cubeAverageFiniteShellEntrySq, hscale]
  exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (originCube d l) (Int.toNat (l - s))
      (fun x => (finiteShellIncrement omega n m x i j) ^ 2)
      (integrableOn_finiteShellEntrySq l n m i j omega)

/-- The normalized restriction descendant average is exactly the original
entry-square cube average. -/
theorem descendantAverage_regFieldEntrySqMassRep_eq_cubeAverage
    (i j : Fin d) {l s : ℤ} (hsl : s ≤ l) {r : ℝ} (hr : r ≠ 0)
    (hrs : r = (3 : ℝ) ^ s) (n m : ℤ) (omega : ShellSeq d) :
    Book.Ch04.restrictionDescendantAverage 0 (l - s)
        (regFieldEntrySqMassRep i j)
        (smulReg r hr (finiteShellIncrement omega n m)) =
      cubeAverageFiniteShellEntrySq l n m i j omega := by
  classical
  rw [cubeAverageFiniteShellEntrySq_eq_descendantAverage_of_scale hsl n m i j omega,
    descendantsAtScale_originCube_eq_image_dilateCube (d := d) hsl,
    Finset.sum_image (fun _R _ _S _ h => dilateCube_injective s h),
    Finset.card_image_of_injective _ (dilateCube_injective s),
    Book.Ch04.restrictionDescendantAverage]
  congr 1
  exact Finset.sum_congr rfl fun Q _ =>
    regFieldEntrySqMassRep_cubeSet_smulReg_eq_cubeAverage i j s hr hrs Q
      (finiteShellIncrement omega n m)
      (fun p q => continuous_finiteShellIncrement_entry omega n m p q)

/-- A squared entry average is dominated by the operator-norm square mass. -/
theorem cubeAverageFiniteShellEntrySq_le_streamIncrementLpMass_two
    (l n m : ℤ) (i j : Fin d) (omega : ShellSeq d) :
    cubeAverageFiniteShellEntrySq l n m i j omega ≤
      streamIncrementLpMass 2 l n m omega := by
  rw [streamIncrementLpMass_eq_cubeAverage (by norm_num)]
  unfold cubeAverageFiniteShellEntrySq cubeAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (cubeVolume_pos _).le)
  refine setIntegral_mono_on
    (integrableOn_finiteShellEntrySq l n m i j omega)
    (integrableOn_cubeSet_streamIncrementLpDensity (by norm_num)
      (originCube d l) n m omega)
    (measurableSet_cubeSet (originCube d l)) ?_
  intro x _
  have hentry := Book.Ch02.abs_entry_le_matrixOperatorNorm
    (finiteShellIncrement omega n m x) i j
  have hsquare := (sq_le_sq₀ (abs_nonneg _)
    (Book.Ch02.matrixOperatorNorm_nonneg _)).2 hentry
  simpa only [streamIncrementLpDensity, Real.rpow_two, sq_abs] using hsquare

/-- At the normalized increment field, the unit-cube entry representative is
the original entry-square average at scale `m+c`. -/
theorem regFieldEntrySqMassRep_originCube_zero_partitionIncrement
    (i j : Fin d) (n m : ℤ) (omega : ShellSeq d) :
    regFieldEntrySqMassRep i j (cubeSet (originCube d 0))
        (smulReg (incrementPartitionScale d m) (incrementPartitionScale_ne_zero d m)
          (finiteShellIncrement omega n m)) =
      cubeAverageFiniteShellEntrySq
        (m + (incrementPartitionShift d : ℤ)) n m i j omega := by
  simpa [cubeAverageFiniteShellEntrySq] using
    regFieldEntrySqMassRep_cubeSet_smulReg_eq_cubeAverage i j
      (m + (incrementPartitionShift d : ℤ))
      (incrementPartitionScale_ne_zero d m) rfl (originCube d 0)
      (finiteShellIncrement omega n m)
      (fun p q => continuous_finiteShellIncrement_entry omega n m p q)

/-- The centered origin observable for one squared entry of a normalized
single shell has a `Gamma_1` tail at the existing one-shell mass scale. -/
theorem isBigO_gammaSigma_centeredOriginObservable_regFieldEntrySqMassRep
    (M : ABKModel d) (k : ℤ) (i j : Fin d) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M (k - 1) k)
      (Book.Ch04.gammaSigma 1)
      (Book.Ch04.restrictionCenteredOriginObservable
        (partitionStreamIncrementLaw M (k - 1) k) 0
        (regFieldEntrySqMassRep i j))
      (streamIncrementLpMassScale M 2 (k - 1) k) := by
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d k) (incrementPartitionScale_ne_zero d k)
      (finiteShellIncrement omega (k - 1) k)
  let g : RegCoeffField d → ℝ :=
    regFieldEntrySqMassRep i j (cubeSet (originCube d 0))
  let K : ℝ := streamIncrementLpMassScale M 2 (k - 1) k
  have hnm : k - 1 < k := by omega
  have hF : Measurable F := measurable_partitionIncrementField (d := d) (k - 1) k
  have hg : Measurable g := measurable_regFieldEntrySqMassRep _ i j
  have hread : ∀ omega, g (F omega) =
      cubeAverageFiniteShellEntrySq
        (k + (incrementPartitionShift d : ℤ)) (k - 1) k i j omega := by
    intro omega
    exact regFieldEntrySqMassRep_originCube_zero_partitionIncrement i j
      (k - 1) k omega
  have hle : ∀ omega, g (F omega) ≤
      streamIncrementLpMass 2 (k + (incrementPartitionShift d : ℤ))
        (k - 1) k omega := by
    intro omega
    rw [hread omega]
    exact cubeAverageFiniteShellEntrySq_le_streamIncrementLpMass_two _ _ _ i j omega
  have hrawComp : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 1) (fun omega => g (F omega)) K :=
    by
      have hmass :=
        (isBigOWith_gammaSigma_streamIncrementLpMass M (p := 2) (by norm_num) hnm
          (k + (incrementPartitionShift d : ℤ))).of_le hle
      simpa only [show (2 : ℝ) / 2 = 1 by norm_num, K] using hmass
  have hraw : IndependentSums.IsBigOWith
      (partitionStreamIncrementLaw M (k - 1) k)
      (IndependentSums.gammaSigma 1) g K := by
    rw [partitionStreamIncrementLaw_eq_map]
    exact isBigOWith_map_of_isBigOWith_comp M.P.toMeasure hF hg hrawComp
  have hstreamInt : Integrable
      (streamIncrementLpMass 2 (k + (incrementPartitionShift d : ℤ))
        (k - 1) k) M.P.toMeasure :=
    integrable_streamIncrementLpMass M (by norm_num) hnm _
  have hcompInt : Integrable (fun omega => g (F omega)) M.P.toMeasure := by
    refine Integrable.mono' hstreamInt (hg.comp hF).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (regFieldEntrySqMassRep_nonneg i j _ (F omega))]
    exact hle omega
  let c : ℝ := ∫ a, g a ∂(partitionStreamIncrementLaw M (k - 1) k)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact integral_nonneg fun a => regFieldEntrySqMassRep_nonneg i j _ a
  have hcK : c ≤ K := by
    dsimp [c]
    rw [partitionStreamIncrementLaw_eq_map,
      integral_map hF.aemeasurable hg.aestronglyMeasurable]
    exact (integral_mono hcompInt hstreamInt hle).trans
      (integral_streamIncrementLpMass_le_massScale M (by norm_num) hnm _)
  exact isBigO_sub_const_of_isBigOWith_of_nonneg hc0 hcK
    (fun a => regFieldEntrySqMassRep_nonneg i j _ a) hraw

/-- CoarseGraining's partition theorem applied to one squared entry of a single
shell. -/
theorem isBigO_gammaSigma_centeredDescendantAverage_regFieldEntrySqMassRep
    (M : ABKModel d) (k : ℤ) (i j : Fin d) {l : ℤ}
    (hlarge : k + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.IsBigO (partitionStreamIncrementLaw M (k - 1) k)
      (Book.Ch04.gammaSigma 1)
      (Book.Ch04.restrictionCenteredDescendantAverage
        (partitionStreamIncrementLaw M (k - 1) k) 0
        (l - (k + (incrementPartitionShift d : ℤ)))
        (regFieldEntrySqMassRep i j))
      (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
        Book.Ch04.partitionCardinalityScale (d := d) 0
          (l - (k + (incrementPartitionShift d : ℤ))) *
        streamIncrementLpMassScale M 2 (k - 1) k) := by
  exact Book.Ch04.isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw
    (le_refl (0 : ℤ)) (by omega)
    (partitionStreamIncrementLaw_stationary M (k - 1) k)
    (partitionStreamIncrementLaw_unitRangeDependent M (k - 1) k)
    (regFieldEntrySqMassRep i j)
    (fun R _ => isLocalRandomVariable_regFieldEntrySqMassRep
      (measurableSet_cubeSet R) i j)
    (isTranslationCovariantR_regFieldEntrySqMassRep i j)
    (measurable_regFieldEntrySqMassRep _ i j)
    (fun R _ => measurable_regFieldEntrySqMassRep _ i j)
    (by norm_num) (by norm_num)
    (streamIncrementLpMassScale_pos M (by norm_num) (by omega))
    (isBigO_gammaSigma_centeredOriginObservable_regFieldEntrySqMassRep M k i j)

/-- Transport the one-entry descendant fluctuation back to the actual shell
sequence.  The centering constant is the unit-cube mean under the normalized
single-shell law and is discharged internally by the later diagonal sum. -/
theorem isBigO_gammaSigma_cubeAverageFiniteShellEntrySq_sub_partitionMean
    (M : ABKModel d) (k : ℤ) (i j : Fin d) {l : ℤ}
    (hlarge : k + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeAverageFiniteShellEntrySq l (k - 1) k i j omega -
          ∫ a, regFieldEntrySqMassRep i j (cubeSet (originCube d 0)) a
            ∂(partitionStreamIncrementLaw M (k - 1) k))
      (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
        Book.Ch04.partitionCardinalityScale (d := d) 0
          (l - (k + (incrementPartitionShift d : ℤ))) *
        streamIncrementLpMassScale M 2 (k - 1) k) := by
  let P := partitionStreamIncrementLaw M (k - 1) k
  let jdepth : ℤ := l - (k + (incrementPartitionShift d : ℤ))
  let X := regFieldEntrySqMassRep i j
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d k) (incrementPartitionScale_ne_zero d k)
      (finiteShellIncrement omega (k - 1) k)
  have hmain :=
    isBigO_gammaSigma_centeredDescendantAverage_regFieldEntrySqMassRep
      M k i j hlarge
  have hg : Measurable
      (Book.Ch04.restrictionCenteredDescendantAverage P 0 jdepth X) := by
    unfold Book.Ch04.restrictionCenteredDescendantAverage
    exact (Finset.measurable_sum _ fun R _ =>
      (measurable_regFieldEntrySqMassRep (cubeSet R) i j).sub
        measurable_const).const_mul _
  have htrans := isBigOWith_comp_of_isBigO_map M.P.toMeasure
    (measurable_partitionIncrementField (d := d) (k - 1) k) hg hmain
  have hQ : (0 : ℤ) ≤ (originCube d jdepth).scale := by
    simpa [originCube, jdepth] using
      (by omega : (0 : ℤ) ≤ l - (k + (incrementPartitionShift d : ℤ)))
  have hsub :=
    Book.Ch04.restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
      (P := P) (Q := originCube d jdepth) (n := 0) hQ X
  have hcenter : ∀ omega : ShellSeq d,
      Book.Ch04.restrictionCenteredDescendantAverage P 0 jdepth X (F omega) =
        cubeAverageFiniteShellEntrySq l (k - 1) k i j omega -
          ∫ a, X (cubeSet (originCube d 0)) a ∂P := by
    intro omega
    have h1 :
        Book.Ch04.restrictionCenteredDescendantAverage P 0 jdepth X (F omega) =
          Book.Ch04.restrictionDescendantAverage 0 jdepth X (F omega) -
            ∫ a, X (cubeSet (originCube d 0)) a ∂P :=
      congrFun hsub (F omega)
    rw [h1, descendantAverage_regFieldEntrySqMassRep_eq_cubeAverage i j
      hlarge (incrementPartitionScale_ne_zero d k) rfl (k - 1) k omega]
  have hfun : (fun omega : ShellSeq d =>
      |Book.Ch04.restrictionCenteredDescendantAverage P 0 jdepth X (F omega)|) =
      fun omega : ShellSeq d =>
        |cubeAverageFiniteShellEntrySq l (k - 1) k i j omega -
          ∫ a, X (cubeSet (originCube d 0)) a ∂P| := by
    funext omega
    rw [hcenter omega]
  change IndependentSums.IsBigOWith M.P.toMeasure (Book.Ch04.gammaSigma 1)
    (fun omega : ShellSeq d =>
      |cubeAverageFiniteShellEntrySq l (k - 1) k i j omega -
        ∫ a, X (cubeSet (originCube d 0)) a ∂P|) _
  rw [← hfun]
  exact htrans

/-- In the large-partition regime the literal squared-entry cube average is
measurable on the shell carrier. -/
theorem measurable_cubeAverageFiniteShellEntrySq_of_large
    (k : ℤ) (i j : Fin d) {l : ℤ}
    (hlarge : k + (incrementPartitionShift d : ℤ) ≤ l) :
    Measurable (cubeAverageFiniteShellEntrySq l (k - 1) k i j) := by
  let X := regFieldEntrySqMassRep i j
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d k) (incrementPartitionScale_ne_zero d k)
      (finiteShellIncrement omega (k - 1) k)
  let jdepth : ℤ := l - (k + (incrementPartitionShift d : ℤ))
  have hdesc : Measurable (Book.Ch04.restrictionDescendantAverage 0 jdepth X) := by
    unfold Book.Ch04.restrictionDescendantAverage
    exact (Finset.measurable_sum _ fun R _ =>
      measurable_regFieldEntrySqMassRep (cubeSet R) i j).const_mul _
  have heq : (fun omega : ShellSeq d =>
      Book.Ch04.restrictionDescendantAverage 0 jdepth X (F omega)) =
      cubeAverageFiniteShellEntrySq l (k - 1) k i j := by
    funext omega
    exact descendantAverage_regFieldEntrySqMassRep_eq_cubeAverage i j hlarge
      (incrementPartitionScale_ne_zero d k) rfl (k - 1) k omega
  rw [← heq]
  exact hdesc.comp (measurable_partitionIncrementField (d := d) (k - 1) k)

/-- The full Frobenius cube mass of a finite shell increment, on the half-open cube
carrier used by the partition A. -/
def cubeFrobeniusMassFiniteShellIncrement (l n m : ℤ)
    (omega : ShellSeq d) : ℝ :=
  cubeAverage (originCube d l)
    (fun x => matrixFrobeniusNormSq (finiteShellIncrement omega n m x))

/-- Frobenius mass is the finite sum of the scalar squared-entry masses. -/
theorem cubeFrobeniusMassFiniteShellIncrement_eq_sum_entrySq
    (l n m : ℤ) (omega : ShellSeq d) :
    cubeFrobeniusMassFiniteShellIncrement l n m omega =
      ∑ p : Fin d × Fin d, cubeAverageFiniteShellEntrySq l n m p.1 p.2 omega := by
  rw [cubeFrobeniusMassFiniteShellIncrement, cubeAverage]
  have hint : ∀ p : Fin d × Fin d,
      IntegrableOn (fun x => (finiteShellIncrement omega n m x p.1 p.2) ^ 2)
        (cubeSet (originCube d l)) volume :=
    fun p => integrableOn_finiteShellEntrySq l n m p.1 p.2 omega
  have hsum :
      ∫ x in cubeSet (originCube d l),
          matrixFrobeniusNormSq (finiteShellIncrement omega n m x) ∂volume =
        ∑ p : Fin d × Fin d,
          ∫ x in cubeSet (originCube d l),
            (finiteShellIncrement omega n m x p.1 p.2) ^ 2 ∂volume := by
    change (∫ x in cubeSet (originCube d l),
      ∑ i : Fin d, ∑ j : Fin d,
        (finiteShellIncrement omega n m x i j) ^ 2 ∂volume) = _
    rw [integral_finset_sum]
    · calc
        (∑ i : Fin d, ∫ x in cubeSet (originCube d l),
            ∑ j : Fin d, (finiteShellIncrement omega n m x i j) ^ 2 ∂volume) =
            ∑ i : Fin d, ∑ j : Fin d,
              ∫ x in cubeSet (originCube d l),
                (finiteShellIncrement omega n m x i j) ^ 2 ∂volume := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_finset_sum]
          intro j _
          exact hint (i, j)
        _ = ∑ p : Fin d × Fin d,
              ∫ x in cubeSet (originCube d l),
                (finiteShellIncrement omega n m x p.1 p.2) ^ 2 ∂volume := by
          rw [Fintype.sum_prod_type]
    · intro i _
      exact integrable_finset_sum _ fun j _ => hint (i, j)
  rw [hsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by
    rw [cubeAverageFiniteShellEntrySq, cubeAverage]

/-- The half-open cube representative agrees with the source-facing open-cube
average. -/
theorem cubeFrobeniusMassFiniteShellIncrement_eq_average
    (l n m : ℤ) (omega : ShellSeq d) :
    cubeFrobeniusMassFiniteShellIncrement l n m omega =
      Book.Ch02.average (Book.Ch02.cubeDomain (originCube d l))
        (fun x => matrixFrobeniusNormSq (finiteShellIncrement omega n m x)) := by
  rw [cubeFrobeniusMassFiniteShellIncrement, cubeAverage, Book.Ch02.average,
    Book.Ch02.cubeDomain_coe, volume_openCubeSet_toReal,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

private theorem integrable_cubeAverageFiniteShellEntrySq_partitionScale
    (M : ABKModel d) (k : ℤ) (i j : Fin d) :
    Integrable
      (cubeAverageFiniteShellEntrySq
        (k + (incrementPartitionShift d : ℤ)) (k - 1) k i j)
      M.P.toMeasure := by
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d k) (incrementPartitionScale_ne_zero d k)
      (finiteShellIncrement omega (k - 1) k)
  have hread : ∀ omega,
      cubeAverageFiniteShellEntrySq
          (k + (incrementPartitionShift d : ℤ)) (k - 1) k i j omega =
        regFieldEntrySqMassRep i j (cubeSet (originCube d 0)) (F omega) := by
    intro omega
    exact (regFieldEntrySqMassRep_originCube_zero_partitionIncrement
      i j (k - 1) k omega).symm
  have hmass : Integrable
      (streamIncrementLpMass 2 (k + (incrementPartitionShift d : ℤ))
        (k - 1) k) M.P.toMeasure :=
    integrable_streamIncrementLpMass M (by norm_num) (by omega) _
  refine Integrable.mono' hmass
    (measurable_cubeAverageFiniteShellEntrySq_of_large
      k i j (le_refl _)).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    rw [hread omega]
    exact regFieldEntrySqMassRep_nonneg i j _ (F omega))]
  exact cubeAverageFiniteShellEntrySq_le_streamIncrementLpMass_two
    _ _ _ i j omega

/-- The sum of the actual normalized single-shell law means is the paper's
exact diagonal one-shell mean.  In particular, the partition transport does
not change the deterministic `cstarPlus` center. -/
theorem sum_partitionStreamIncrementLaw_entrySqMeans_eq
    (M : ABKModel d) (k : ℤ) :
    (∑ p : Fin d × Fin d,
        ∫ a, regFieldEntrySqMassRep p.1 p.2 (cubeSet (originCube d 0)) a
          ∂(partitionStreamIncrementLaw M (k - 1) k)) =
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) := by
  classical
  let F : ShellSeq d → RegCoeffField d := fun omega =>
    smulReg (incrementPartitionScale d k) (incrementPartitionScale_ne_zero d k)
      (finiteShellIncrement omega (k - 1) k)
  have hF : Measurable F :=
    measurable_partitionIncrementField (d := d) (k - 1) k
  have hmean : ∀ p : Fin d × Fin d,
      (∫ a, regFieldEntrySqMassRep p.1 p.2 (cubeSet (originCube d 0)) a
          ∂(partitionStreamIncrementLaw M (k - 1) k)) =
        ∫ omega,
          cubeAverageFiniteShellEntrySq
            (k + (incrementPartitionShift d : ℤ)) (k - 1) k p.1 p.2 omega
          ∂M.P.toMeasure := by
    intro p
    rw [partitionStreamIncrementLaw_eq_map,
      integral_map hF.aemeasurable
        (measurable_regFieldEntrySqMassRep _ p.1 p.2).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun omega =>
      regFieldEntrySqMassRep_originCube_zero_partitionIncrement
        p.1 p.2 (k - 1) k omega)
  rw [Finset.sum_congr rfl (fun p _ => hmean p),
    ← integral_finset_sum Finset.univ (fun p _ =>
      integrable_cubeAverageFiniteShellEntrySq_partitionScale M k p.1 p.2)]
  have hsum : (fun omega : ShellSeq d =>
      ∑ p : Fin d × Fin d,
        cubeAverageFiniteShellEntrySq
          (k + (incrementPartitionShift d : ℤ)) (k - 1) k p.1 p.2 omega) =
      cubeFrobeniusMassFiniteShellIncrement
        (k + (incrementPartitionShift d : ℤ)) (k - 1) k := by
    funext omega
    exact (cubeFrobeniusMassFiniteShellIncrement_eq_sum_entrySq
      (k + (incrementPartitionShift d : ℤ)) (k - 1) k omega).symm
  rw [hsum]
  have hioc : Finset.Ioc (k - 1) k = {k} := by
    ext q
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  calc
    ∫ omega,
        cubeFrobeniusMassFiniteShellIncrement
          (k + (incrementPartitionShift d : ℤ)) (k - 1) k omega
        ∂M.P.toMeasure =
      ∫ omega,
        Book.Ch02.average
          (Book.Ch02.cubeDomain
            (originCube d (k + (incrementPartitionShift d : ℤ))))
          (fun x => matrixFrobeniusNormSq
            (finiteShellIncrement omega (k - 1) k x)) ∂M.P.toMeasure := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun omega =>
            cubeFrobeniusMassFiniteShellIncrement_eq_average
              (k + (incrementPartitionShift d : ℤ)) (k - 1) k omega)
    _ = ∑ q ∈ Finset.Ioc (k - 1) k,
          (3 : ℝ) ^ (2 * M.gamma * (q : ℝ)) *
            (Disorder.cstarPlus M * Real.log 3) :=
      integral_average_frobeniusMass_finiteShellIncrement M
        (k + (incrementPartitionShift d : ℤ)) (k - 1) k
    _ = (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (Disorder.cstarPlus M * Real.log 3) := by
      rw [hioc]
      simp

/-- Raw large-partition diagonal fluctuation: the sum of all entry-square
averages centered by their normalized-law means.  Every condition is derived
from the model and the scale range; no analytic obligation is exposed. -/
theorem isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_partitionMeans
    (M : ABKModel d) (k : ℤ) {l : ℤ}
    (hlarge : k + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
          ∑ p : Fin d × Fin d,
            ∫ a, regFieldEntrySqMassRep p.1 p.2 (cubeSet (originCube d 0)) a
              ∂(partitionStreamIncrementLaw M (k - 1) k))
      (IndependentSums.gammaTriangleConst 1 * (d : ℝ) ^ 2 *
        (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
          Book.Ch04.partitionCardinalityScale (d := d) 0
            (l - (k + (incrementPartitionShift d : ℤ))) *
          streamIncrementLpMassScale M 2 (k - 1) k)) := by
  let A : ℝ := Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
    Book.Ch04.partitionCardinalityScale (d := d) 0
      (l - (k + (incrementPartitionShift d : ℤ))) *
    streamIncrementLpMassScale M 2 (k - 1) k
  let X : Fin d × Fin d → ShellSeq d → ℝ := fun p omega =>
    cubeAverageFiniteShellEntrySq l (k - 1) k p.1 p.2 omega -
      ∫ a, regFieldEntrySqMassRep p.1 p.2 (cubeSet (originCube d 0)) a
        ∂(partitionStreamIncrementLaw M (k - 1) k)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hs : (Finset.univ : Finset (Fin d × Fin d)).Nonempty := by
    let i : Fin d := ⟨0, hd⟩
    exact ⟨(i, i), Finset.mem_univ _⟩
  have hcardPos : 0 < Book.Ch04.partitionCardinalityScale (d := d) 0
      (l - (k + (incrementPartitionShift d : ℤ))) := by
    unfold Book.Ch04.partitionCardinalityScale
    have hdepth : (0 : ℤ) ≤ l - (k + (incrementPartitionShift d : ℤ)) := by
      omega
    have hn : 0 < ((descendantsAtScale
        (originCube d (l - (k + (incrementPartitionShift d : ℤ)))) 0).card : ℝ) := by
      exact_mod_cast (descendantsAtScale_nonempty _
        (by simpa [originCube] using hdepth)).card_pos
    exact div_pos (Real.sqrt_pos.2 hn) hn
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos
      (mul_pos (Book.Ch04.gammaSigmaDescendantsAtScaleConst_pos (by norm_num))
        hcardPos)
      (streamIncrementLpMassScale_pos M (by norm_num) (by omega))
  have hsum := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (s := (Finset.univ : Finset (Fin d × Fin d)))
    (X := X) (a := fun _ => A) (σ := 1) (by norm_num) hs
    (fun _ _ => hA)
    (fun p _ => isBigO_gammaSigma_cubeAverageFiniteShellEntrySq_sub_partitionMean
      M k p.1 p.2 hlarge)
    (fun p _ => (measurable_cubeAverageFiniteShellEntrySq_of_large
      k p.1 p.2 hlarge).sub measurable_const)
  have hXsum : (fun omega => ∑ p : Fin d × Fin d, X p omega) =
      fun omega => cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
        ∑ p : Fin d × Fin d,
          ∫ a, regFieldEntrySqMassRep p.1 p.2 (cubeSet (originCube d 0)) a
            ∂(partitionStreamIncrementLaw M (k - 1) k) := by
    funext omega
    rw [cubeFrobeniusMassFiniteShellIncrement_eq_sum_entrySq,
      Finset.sum_sub_distrib]
  have hAsum : ∑ _p : Fin d × Fin d, A = (d : ℝ) ^ 2 * A := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
    push_cast
    ring
  rw [hXsum, hAsum] at hsum
  simpa only [A, mul_assoc] using hsum

/-- A dimension-only upper envelope for the `p=2` mass scale of one shell. -/
noncomputable def singleShellLpMassConst (d : ℕ) : ℝ :=
  1 + 2 * Real.exp 1 * (IndependentSums.gammaMomentConst 2) ^ 2 *
    (IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
      geometricConcentrationConst) ^ 2

theorem singleShellLpMassConst_pos (d : ℕ) : 0 < singleShellLpMassConst d := by
  unfold singleShellLpMassConst
  positivity

/-- The generic increment mass bound specializes to a log-free one-shell
scale. -/
theorem streamIncrementLpMassScale_two_singleShell_le
    (M : ABKModel d) (k : ℤ) :
    streamIncrementLpMassScale M 2 (k - 1) k ≤
      singleShellLpMassConst d * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
  have hnm : k - 1 < k := by omega
  have hmin : min M.gamma⁻¹ ((k : ℝ) - ((k - 1 : ℤ) : ℝ)) ≤ 1 := by
    norm_num
  have hgeom : 0 ≤ (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [streamIncrementLpMassScale, Real.rpow_two, mul_pow,
    streamPointScale_sq M hnm]
  let core : ℝ :=
    2 * Real.exp 1 * (IndependentSums.gammaMomentConst 2) ^ 2 *
      (IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
        geometricConcentrationConst) ^ 2
  have hcore : 0 ≤ core := by dsimp [core]; positivity
  have heq :
      Real.exp 1 *
          ((IndependentSums.gammaMomentConst 2) ^ 2 *
            ((IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
                geometricConcentrationConst) ^ 2 *
              (min M.gamma⁻¹ ((k : ℝ) - ((k - 1 : ℤ) : ℝ)) *
                (3 : ℝ) ^ (2 * (M.gamma * (k : ℝ))))) *
            (2 : ℝ) ^ ((2 : ℝ) / 2)) =
        core *
          (min M.gamma⁻¹ ((k : ℝ) - ((k - 1 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
    rw [show (2 : ℝ) ^ ((2 : ℝ) / 2) = 2 by norm_num]
    dsimp [core]
    ring_nf
  rw [heq]
  calc
    core * (min M.gamma⁻¹ ((k : ℝ) - ((k - 1 : ℤ) : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))
        ≤ core * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa using mul_le_of_le_one_left hgeom hmin) hcore
    _ ≤ singleShellLpMassConst d *
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hgeom
          dsimp [singleShellLpMassConst, core]
          linarith

/-- The dimension-only constant for the sharp large-partition diagonal
fluctuation.  The `1` makes positivity independent of vacuous dimensions. -/
noncomputable def layerDiagonalLargeConst (d : ℕ) : ℝ :=
  1 + IndependentSums.gammaTriangleConst 1 * (d : ℝ) ^ 2 *
    Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
    (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
    singleShellLpMassConst d

/-- **Sharp diagonal large-cube endpoint.**  The centered one-shell Frobenius
mass has exactly the finer-shell spatial gain needed by the corrected
`e.km.kn.L2.bound`; the normalization shift is absorbed into one constant
depending only on `d`. -/
theorem isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_partitionMeans_sharp
    (M : ABKModel d) (k : ℤ) {l : ℤ}
    (hlarge : k + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
          ∑ p : Fin d × Fin d,
            ∫ a, regFieldEntrySqMassRep p.1 p.2 (cubeSet (originCube d 0)) a
              ∂(partitionStreamIncrementLaw M (k - 1) k))
      (layerDiagonalLargeConst d *
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ)))) := by
  have hraw :=
    isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_partitionMeans
      M k hlarge
  apply hraw.mono_scale
  have hj : (0 : ℤ) ≤ l - (k + (incrementPartitionShift d : ℤ)) := by omega
  rw [partitionCardinalityScale_originCube_zero (d := d) hj]
  have hcast :
      ((l - (k + (incrementPartitionShift d : ℤ)) : ℤ) : ℝ) =
        (l : ℝ) - ((k + (incrementPartitionShift d : ℤ)) : ℝ) := by
    push_cast
    ring_nf
  rw [hcast]
  have hshift :
      (3 : ℝ) ^
          (-((d : ℝ) / 2) *
            ((l : ℝ) - ((k + (incrementPartitionShift d : ℤ)) : ℝ))) =
        (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring_nf
  rw [hshift]
  let core : ℝ := IndependentSums.gammaTriangleConst 1 * (d : ℝ) ^ 2 *
    Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
    (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
    singleShellLpMassConst d
  let geom : ℝ := (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))
  let gain : ℝ := (3 : ℝ) ^
    (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ)))
  let pre : ℝ := IndependentSums.gammaTriangleConst 1 * (d : ℝ) ^ 2 *
    Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
    (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ))
  have hpre : 0 ≤ pre := by
    dsimp [pre]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg IndependentSums.gammaTriangleConst_pos.le (sq_nonneg _))
        (Book.Ch04.gammaSigmaDescendantsAtScaleConst_pos (by norm_num)).le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcore : 0 ≤ core := by
    dsimp [core, pre] at hpre ⊢
    exact mul_nonneg hpre (singleShellLpMassConst_pos d).le
  have hgeom : 0 ≤ geom := by dsimp [geom]; positivity
  have hgain : 0 ≤ gain := by dsimp [gain]; positivity
  calc
    IndependentSums.gammaTriangleConst 1 * (d : ℝ) ^ 2 *
          (Book.Ch04.gammaSigmaDescendantsAtScaleConst d 0 1 *
            ((3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
              gain) * streamIncrementLpMassScale M 2 (k - 1) k)
        = pre * streamIncrementLpMassScale M 2 (k - 1) k * gain := by
          dsimp [pre]
          ring_nf
    _ ≤ pre * (singleShellLpMassConst d * geom) * gain := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (streamIncrementLpMassScale_two_singleShell_le M k) hpre) hgain
    _ = core * geom * gain := by
          dsimp [pre, core]
          ring_nf
    _ ≤ (1 + core) * geom * gain := by
          gcongr
          exact le_add_of_nonneg_left zero_le_one
    _ = layerDiagonalLargeConst d *
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ))) := by
          simp only [layerDiagonalLargeConst, core, geom, gain]

/-- The sharp large-partition diagonal estimate with the implementation center
eliminated in favor of the paper's exact one-shell expectation.  This is a
directly consumable diagonal input for the later two-gap shell summation; it
does not include the distinct off-diagonal pairing estimate. -/
theorem isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_exactMean_sharp
    (M : ABKModel d) (k : ℤ) {l : ℤ}
    (hlarge : k + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.IsBigO M.P.toMeasure (Book.Ch04.gammaSigma 1)
      (fun omega : ShellSeq d =>
        cubeFrobeniusMassFiniteShellIncrement l (k - 1) k omega -
          (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
            (Disorder.cstarPlus M * Real.log 3))
      (layerDiagonalLargeConst d *
        (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (k : ℝ)))) := by
  simpa only [sum_partitionStreamIncrementLaw_entrySqMeans_eq] using
    isBigO_gammaSigma_cubeFrobeniusMassFiniteShellIncrement_sub_partitionMeans_sharp
      M k hlarge

end

end Algsuperdiff.Section3.Provider.Stream
