import Algsuperdiff.Section3.Provider.Stream.FrobeniusMassRepresentative
import Algsuperdiff.Section3.Cutoff.CoefficientLocality

/-!
# A measurable Frobenius-pairing representative

This module supplies the jointly measurable polarization representative used
internally in the corrected off-diagonal shell-pair argument for ABK26
`e.km.kn.L2.bound`.  It agrees with the literal cube pairing on continuous
fields and exposes the local measurability needed by restriction-law coloring.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open Homogenization Homogenization.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The literal cube-averaged Frobenius mass of a regular matrix field. -/
def cubeFrobeniusMassReg (Q : TriadicCube d) (a : RegCoeffField d) : ℝ :=
  cubeAverage Q (fun x => matrixFrobeniusNormSq (a x))

/-- The literal cube-averaged Frobenius pairing of two regular fields. -/
def cubeFrobeniusPairingReg (Q : TriadicCube d)
    (a b : RegCoeffField d) : ℝ :=
  cubeAverage Q (fun x => ∑ i, ∑ j, a x i j * b x i j)

/-- A globally measurable Frobenius-mass representative. -/
def regFieldFrobeniusMassRep (U : Set (Vec d)) (a : RegCoeffField d) : ℝ :=
  ∑ p : Fin d × Fin d, regFieldEntrySqMassRep p.1 p.2 U a

theorem measurable_regFieldFrobeniusMassRep_localSigmaR (U : Set (Vec d)) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
      (regFieldFrobeniusMassRep U) := by
  unfold regFieldFrobeniusMassRep
  exact Finset.measurable_sum _ fun p _ =>
    measurable_regFieldEntrySqMassRep_localSigmaR U p.1 p.2

theorem measurable_regFieldFrobeniusMassRep (U : Set (Vec d)) :
    Measurable (regFieldFrobeniusMassRep (d := d) U) :=
  (measurable_regFieldFrobeniusMassRep_localSigmaR U).mono
    (LocalSigmaR_le U) le_rfl

/-- Polarization of the square-mass representative. -/
def regFieldEntryPairingRep (i j : Fin d) (U : Set (Vec d))
    (a b : RegCoeffField d) : ℝ :=
  (regFieldEntrySqMassRep i j U (a + b) -
      regFieldEntrySqMassRep i j U a -
      regFieldEntrySqMassRep i j U b) / 2

/-- The finite sum of the entrywise polarization representatives. -/
def regFieldFrobeniusPairingRep (U : Set (Vec d))
    (a b : RegCoeffField d) : ℝ :=
  ∑ p : Fin d × Fin d, regFieldEntryPairingRep p.1 p.2 U a b

theorem measurable_regFieldEntryPairingRep_comp
    {Omega : Type*} [MeasurableSpace Omega] (U : Set (Vec d)) (i j : Fin d)
    {a b : Omega → RegCoeffField d} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun omega => regFieldEntryPairingRep i j U (a omega) (b omega)) := by
  unfold regFieldEntryPairingRep
  exact ((((measurable_regFieldEntrySqMassRep U i j).comp (ha.add hb)).sub
    ((measurable_regFieldEntrySqMassRep U i j).comp ha)).sub
    ((measurable_regFieldEntrySqMassRep U i j).comp hb)).div_const 2

theorem measurable_regFieldFrobeniusPairingRep_comp
    {Omega : Type*} [MeasurableSpace Omega] (U : Set (Vec d))
    {a b : Omega → RegCoeffField d} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun omega => regFieldFrobeniusPairingRep U (a omega) (b omega)) := by
  unfold regFieldFrobeniusPairingRep
  exact Finset.measurable_sum _ fun p _ =>
    measurable_regFieldEntryPairingRep_comp U p.1 p.2 ha hb

theorem measurable_regFieldFrobeniusPairingRep (U : Set (Vec d)) :
    Measurable (fun p : RegCoeffField d × RegCoeffField d =>
      regFieldFrobeniusPairingRep U p.1 p.2) :=
  measurable_regFieldFrobeniusPairingRep_comp U measurable_fst measurable_snd

/-- With the first field frozen, the pairing reads only the second field on
`U`. -/
theorem measurable_regFieldEntryPairingRep_const_localSigmaR
    (U : Set (Vec d)) (i j : Fin d) (a : RegCoeffField d) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
      (fun b => regFieldEntryPairingRep i j U a b) := by
  unfold regFieldEntryPairingRep
  exact ((((measurable_regFieldEntrySqMassRep_localSigmaR U i j).comp
    (measurable_const_add_local a U)).sub measurable_const).sub
    (measurable_regFieldEntrySqMassRep_localSigmaR U i j)).div_const 2

theorem measurable_regFieldFrobeniusPairingRep_const_localSigmaR
    (U : Set (Vec d)) (a : RegCoeffField d) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
      (fun b => regFieldFrobeniusPairingRep U a b) := by
  unfold regFieldFrobeniusPairingRep
  exact Finset.measurable_sum _ fun p _ =>
    measurable_regFieldEntryPairingRep_const_localSigmaR U p.1 p.2 a

theorem isLocalRandomVariable_regFieldFrobeniusPairingRep_const
    {U : Set (Vec d)} (hU : MeasurableSet U) (a : RegCoeffField d) :
    Book.Ch04.IsRestrictionLocalRandomVariable U hU
      (fun b => regFieldFrobeniusPairingRep U a b) :=
  measurable_restrictionSigmaR_of_measurable_localSigmaR hU
    (measurable_regFieldFrobeniusPairingRep_const_localSigmaR U a)

private theorem continuous_add_entries (a b : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (hb : ∀ i j, Continuous fun x : Vec d => b x i j) :
    ∀ i j, Continuous fun x : Vec d => (a + b) x i j := by
  intro i j
  simpa only [RegCoeffField.add_apply, Matrix.add_apply] using
    (ha i j).add (hb i j)

/-- On continuous fields the mass representative is the literal Frobenius
cube mass. -/
theorem regFieldFrobeniusMassRep_cubeSet_eq
    (Q : TriadicCube d) (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j) :
    regFieldFrobeniusMassRep (cubeSet Q) a = cubeFrobeniusMassReg Q a := by
  rw [regFieldFrobeniusMassRep, cubeFrobeniusMassReg]
  have hint : ∀ p : Fin d × Fin d,
      IntegrableOn (fun x => (a x p.1 p.2) ^ 2) (cubeSet Q) volume :=
    fun p => (ha p.1 p.2).pow 2 |>.continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  simp_rw [regFieldEntrySqMassRep_cubeSet_eq_cubeAverage _ _ Q a ha,
    cubeAverage]
  simp only [matrixFrobeniusNormSq]
  calc
    (∑ p : Fin d × Fin d,
        (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, (a x p.1 p.2) ^ 2 ∂volume) =
        (cubeVolume Q)⁻¹ * ∑ p : Fin d × Fin d,
          ∫ x in cubeSet Q, (a x p.1 p.2) ^ 2 ∂volume := by
      rw [Finset.mul_sum]
    _ = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q,
        ∑ p : Fin d × Fin d, (a x p.1 p.2) ^ 2 ∂volume := by
      rw [integral_finset_sum _ fun p _ => hint p]
    _ = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q,
        ∑ i, ∑ j, (a x i j) ^ 2 ∂volume := by
      congr 2
      funext x
      exact Fintype.sum_prod_type
        (fun p : Fin d × Fin d => (a x p.1 p.2) ^ 2)

/-- Polarizing entry by entry is the same as polarizing the summed mass
representative. -/
theorem regFieldFrobeniusPairingRep_eq_mass_polarization
    (U : Set (Vec d)) (a b : RegCoeffField d) :
    regFieldFrobeniusPairingRep U a b =
      (regFieldFrobeniusMassRep U (a + b) -
        regFieldFrobeniusMassRep U a -
        regFieldFrobeniusMassRep U b) / 2 := by
  unfold regFieldFrobeniusPairingRep regFieldFrobeniusMassRep
    regFieldEntryPairingRep
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- On continuous fields the polarization representative is the literal
Frobenius cube pairing. -/
theorem regFieldFrobeniusPairingRep_cubeSet_eq
    (Q : TriadicCube d) (a b : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (hb : ∀ i j, Continuous fun x : Vec d => b x i j) :
    regFieldFrobeniusPairingRep (cubeSet Q) a b =
      cubeFrobeniusPairingReg Q a b := by
  have hab := continuous_add_entries a b ha hb
  have hintA : IntegrableOn (fun x => matrixFrobeniusNormSq (a x))
      (cubeSet Q) volume :=
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (ha i j).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hintB : IntegrableOn (fun x => matrixFrobeniusNormSq (b x))
      (cubeSet Q) volume :=
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (hb i j).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hintAB : IntegrableOn (fun x => matrixFrobeniusNormSq ((a + b) x))
      (cubeSet Q) volume :=
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (hab i j).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  rw [regFieldFrobeniusPairingRep_eq_mass_polarization,
    regFieldFrobeniusMassRep_cubeSet_eq Q (a + b) hab,
    regFieldFrobeniusMassRep_cubeSet_eq Q a ha,
    regFieldFrobeniusMassRep_cubeSet_eq Q b hb,
    cubeFrobeniusMassReg, cubeFrobeniusMassReg, cubeFrobeniusMassReg,
    cubeFrobeniusPairingReg, cubeAverage, cubeAverage, cubeAverage, cubeAverage]
  have hsubA :
      ∫ x in cubeSet Q,
          matrixFrobeniusNormSq ((a + b) x) - matrixFrobeniusNormSq (a x)
          ∂volume =
        (∫ x in cubeSet Q, matrixFrobeniusNormSq ((a + b) x) ∂volume) -
          ∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume := by
    exact integral_sub hintAB hintA
  have hsubB :
      ∫ x in cubeSet Q,
          (matrixFrobeniusNormSq ((a + b) x) - matrixFrobeniusNormSq (a x)) -
            matrixFrobeniusNormSq (b x) ∂volume =
        (∫ x in cubeSet Q,
          matrixFrobeniusNormSq ((a + b) x) - matrixFrobeniusNormSq (a x)
          ∂volume) -
          ∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume := by
    exact integral_sub (hintAB.sub hintA) hintB
  have hinner :
      ((∫ x in cubeSet Q, matrixFrobeniusNormSq ((a + b) x) ∂volume) -
          (∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume) -
          (∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume)) / 2 =
        ∫ x in cubeSet Q, ∑ i, ∑ j, a x i j * b x i j ∂volume := by
    calc
      ((∫ x in cubeSet Q, matrixFrobeniusNormSq ((a + b) x) ∂volume) -
          (∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume) -
          (∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume)) / 2 =
          ∫ x in cubeSet Q,
            (matrixFrobeniusNormSq ((a + b) x) -
              matrixFrobeniusNormSq (a x) -
              matrixFrobeniusNormSq (b x)) / 2 ∂volume := by
        rw [integral_div, hsubB, hsubA]
      _ = ∫ x in cubeSet Q, ∑ i, ∑ j, a x i j * b x i j ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [RegCoeffField.add_apply, Matrix.add_apply,
          matrixFrobeniusNormSq]
        have hadd :
            (∑ i, ∑ j, (a x i j + b x i j) ^ 2) =
              2 * (∑ i, ∑ j, a x i j * b x i j) +
                (∑ i, ∑ j, (a x i j) ^ 2) +
                (∑ i, ∑ j, (b x i j) ^ 2) := by
          calc
            (∑ i, ∑ j, (a x i j + b x i j) ^ 2) =
                ∑ i, ∑ j,
                  (2 * (a x i j * b x i j) +
                    (a x i j) ^ 2 + (b x i j) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = _ := by
              simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hadd]
        ring
  calc
    ((((cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, matrixFrobeniusNormSq ((a + b) x) ∂volume) -
        (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume) -
      (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume) / 2 =
        (cubeVolume Q)⁻¹ *
          (((∫ x in cubeSet Q, matrixFrobeniusNormSq ((a + b) x) ∂volume) -
           (∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume) -
           (∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume)) / 2) := by
      ring
    _ = (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet Q, ∑ i, ∑ j, a x i j * b x i j ∂volume := by
      exact congrArg ((cubeVolume Q)⁻¹ * ·) hinner

/-- The mass of a spatially rescaled continuous field on a normalized cube is
the literal mass on the corresponding physical cube. -/
theorem regFieldFrobeniusMassRep_cubeSet_smulReg_eq
    (s : ℤ) {r : ℝ} (hr : r ≠ 0) (hrs : r = (3 : ℝ) ^ s)
    (Q : TriadicCube d) (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j) :
    regFieldFrobeniusMassRep (cubeSet Q) (smulReg r hr a) =
      cubeFrobeniusMassReg (dilateCube s Q) a := by
  unfold regFieldFrobeniusMassRep cubeFrobeniusMassReg
  simp_rw [regFieldEntrySqMassRep_cubeSet_smulReg_eq_cubeAverage _ _ s hr hrs Q a ha]
  have hint : ∀ p : Fin d × Fin d,
      IntegrableOn (fun x => (a x p.1 p.2) ^ 2)
        (cubeSet (dilateCube s Q)) volume := fun p =>
    (ha p.1 p.2).pow 2 |>.continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter (dilateCube s Q))
        (cubeRadius (dilateCube s Q))) |>.mono_set
        (cubeSet_subset_closedBall (dilateCube s Q))
  unfold cubeAverage matrixFrobeniusNormSq
  calc
    (∑ p : Fin d × Fin d,
        (cubeVolume (dilateCube s Q))⁻¹ *
          ∫ x in cubeSet (dilateCube s Q), (a x p.1 p.2) ^ 2 ∂volume) =
        (cubeVolume (dilateCube s Q))⁻¹ *
          ∑ p : Fin d × Fin d,
            ∫ x in cubeSet (dilateCube s Q), (a x p.1 p.2) ^ 2 ∂volume := by
      rw [Finset.mul_sum]
    _ = (cubeVolume (dilateCube s Q))⁻¹ *
        ∫ x in cubeSet (dilateCube s Q),
          ∑ p : Fin d × Fin d, (a x p.1 p.2) ^ 2 ∂volume := by
      rw [integral_finset_sum _ fun p _ => hint p]
    _ = (cubeVolume (dilateCube s Q))⁻¹ *
        ∫ x in cubeSet (dilateCube s Q),
          ∑ i, ∑ j, (a x i j) ^ 2 ∂volume := by
      congr 2
      funext x
      exact Fintype.sum_prod_type
        (fun p : Fin d × Fin d => (a x p.1 p.2) ^ 2)

private theorem smulReg_add {r : ℝ} (hr : r ≠ 0)
    (a b : RegCoeffField d) :
    smulReg r hr (a + b) = smulReg r hr a + smulReg r hr b := by
  ext x i j
  simp only [smulReg_apply, RegCoeffField.add_apply, Matrix.add_apply]

/-- The pairing representative of two equally rescaled continuous fields is
the literal physical-cube pairing. -/
theorem regFieldFrobeniusPairingRep_cubeSet_smulReg_eq
    (s : ℤ) {r : ℝ} (hr : r ≠ 0) (hrs : r = (3 : ℝ) ^ s)
    (Q : TriadicCube d) (a b : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (hb : ∀ i j, Continuous fun x : Vec d => b x i j) :
    regFieldFrobeniusPairingRep (cubeSet Q)
        (smulReg r hr a) (smulReg r hr b) =
      cubeFrobeniusPairingReg (dilateCube s Q) a b := by
  have hab := continuous_add_entries a b ha hb
  rw [regFieldFrobeniusPairingRep_eq_mass_polarization,
    ← smulReg_add hr a b,
    regFieldFrobeniusMassRep_cubeSet_smulReg_eq s hr hrs Q (a + b) hab,
    regFieldFrobeniusMassRep_cubeSet_smulReg_eq s hr hrs Q a ha,
    regFieldFrobeniusMassRep_cubeSet_smulReg_eq s hr hrs Q b hb]
  rw [← regFieldFrobeniusPairingRep_cubeSet_eq (dilateCube s Q) a b ha hb,
    regFieldFrobeniusPairingRep_eq_mass_polarization,
    regFieldFrobeniusMassRep_cubeSet_eq (dilateCube s Q) (a + b) hab,
    regFieldFrobeniusMassRep_cubeSet_eq (dilateCube s Q) a ha,
    regFieldFrobeniusMassRep_cubeSet_eq (dilateCube s Q) b hb]

/-- The descendant Frobenius masses of a continuous field sum to the parent
mass times the descendant count. -/
theorem sum_cubeFrobeniusMassReg_descendantsAtScale
    (Q : TriadicCube d) {k : ℤ} (hkQ : k ≤ Q.scale)
    (a : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j) :
    ∑ R ∈ descendantsAtScale Q k, cubeFrobeniusMassReg R a =
      ((descendantsAtScale Q k).card : ℝ) * cubeFrobeniusMassReg Q a := by
  have hint : IntegrableOn (fun x => matrixFrobeniusNormSq (a x))
      (cubeSet Q) volume :=
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (ha i j).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have havg : cubeFrobeniusMassReg Q a =
      ((descendantsAtScale Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q k, cubeFrobeniusMassReg R a := by
    rw [cubeFrobeniusMassReg]
    have hscale : descendantsAtScale Q k =
        descendantsAtDepth Q (Int.toNat (Q.scale - k)) :=
      descendantsAtScale_eq_descendantsAtDepth Q hkQ
    rw [hscale]
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q (Int.toNat (Q.scale - k)) (fun x => matrixFrobeniusNormSq (a x)) hint
  have hcard : ((descendantsAtScale Q k).card : ℝ) ≠ 0 := by
    exact_mod_cast (descendantsAtScale_nonempty Q hkQ).card_ne_zero
  rw [havg]
  field_simp

/-- Descendant averaging is exact for the continuous Frobenius-pairing
representative. -/
theorem descendantAverage_regFieldFrobeniusPairingRep
    (Q : TriadicCube d) {k : ℤ} (hkQ : k ≤ Q.scale)
    (a b : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (hb : ∀ i j, Continuous fun x : Vec d => b x i j) :
    (((descendantsAtScale Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q k,
          regFieldFrobeniusPairingRep (cubeSet R) a b) =
      regFieldFrobeniusPairingRep (cubeSet Q) a b := by
  classical
  have hint : IntegrableOn
      (fun x => ∑ i, ∑ j, a x i j * b x i j) (cubeSet Q) volume :=
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (ha i j).mul (hb i j)).continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
          (cubeSet_subset_closedBall Q)
  have havg : cubeFrobeniusPairingReg Q a b =
      ((descendantsAtScale Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q k, cubeFrobeniusPairingReg R a b := by
    rw [cubeFrobeniusPairingReg]
    have hscale : descendantsAtScale Q k =
        descendantsAtDepth Q (Int.toNat (Q.scale - k)) :=
      descendantsAtScale_eq_descendantsAtDepth Q hkQ
    rw [hscale]
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q (Int.toNat (Q.scale - k)) (fun x => ∑ i, ∑ j, a x i j * b x i j) hint
  rw [regFieldFrobeniusPairingRep_cubeSet_eq Q a b ha hb]
  simp_rw [regFieldFrobeniusPairingRep_cubeSet_eq _ a b ha hb]
  exact havg.symm

/-- Pointwise Frobenius Cauchy--Schwarz. -/
theorem abs_matrixFrobeniusPairing_le (a b : Mat d) :
    |∑ i, ∑ j, a i j * b i j| ≤
      Real.sqrt (matrixFrobeniusNormSq a) *
        Real.sqrt (matrixFrobeniusNormSq b) := by
  classical
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin d × Fin d))
    (fun p => a p.1 p.2) (fun p => b p.1 p.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type] at hCS
  have ha0 : 0 ≤ matrixFrobeniusNormSq a :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul ha0]
  exact Real.sqrt_le_sqrt hCS

/-- Cube-averaged Frobenius Cauchy--Schwarz for continuous fields. -/
theorem abs_cubeFrobeniusPairingReg_le
    (Q : TriadicCube d) (a b : RegCoeffField d)
    (ha : ∀ i j, Continuous fun x : Vec d => a x i j)
    (hb : ∀ i j, Continuous fun x : Vec d => b x i j) :
    |cubeFrobeniusPairingReg Q a b| ≤
      Real.sqrt (cubeFrobeniusMassReg Q a) *
        Real.sqrt (cubeFrobeniusMassReg Q b) := by
  -- This is the scalar integral Cauchy--Schwarz applied to the flattened
  -- matrix entries; the compact cube makes every displayed integral finite.
  let U := cubeSet Q
  let F : Vec d → ℝ := fun x => Real.sqrt (matrixFrobeniusNormSq (a x))
  let G : Vec d → ℝ := fun x => Real.sqrt (matrixFrobeniusNormSq (b x))
  have hFa : Continuous F := by
    apply Real.continuous_sqrt.comp
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (ha i j).pow 2
  have hGb : Continuous G := by
    apply Real.continuous_sqrt.comp
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (hb i j).pow 2
  have hpair : Continuous fun x : Vec d => ∑ i, ∑ j, a x i j * b x i j :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (ha i j).mul (hb i j)
  have hFint : IntegrableOn F U volume :=
    hFa.continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hGint : IntegrableOn G U volume :=
    hGb.continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hFGint : IntegrableOn (fun x => F x * G x) U volume :=
    (hFa.mul hGb).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hPint : IntegrableOn (fun x => ∑ i, ∑ j, a x i j * b x i j) U volume :=
    hpair.continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hpoint : ∀ x, |∑ i, ∑ j, a x i j * b x i j| ≤ F x * G x :=
    fun x => abs_matrixFrobeniusPairing_le (a x) (b x)
  have hstep1 : |∫ x in U, ∑ i, ∑ j, a x i j * b x i j ∂volume| ≤
      ∫ x in U, F x * G x ∂volume := by
    calc
      |∫ x in U, ∑ i, ∑ j, a x i j * b x i j ∂volume| ≤
          ∫ x in U, |∑ i, ∑ j, a x i j * b x i j| ∂volume := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := volume.restrict U)
            (f := fun x => ∑ i, ∑ j, a x i j * b x i j)
      _ ≤ ∫ x in U, F x * G x ∂volume :=
        setIntegral_mono_on hPint.norm hFGint (measurableSet_cubeSet Q)
          fun x _ => hpoint x
  have hF2 : IntegrableOn (fun x => F x ^ 2) U volume :=
    (hFa.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hG2 : IntegrableOn (fun x => G x ^ 2) U volume :=
    (hGb.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
        (cubeSet_subset_closedBall Q)
  have hFmem : MemLp F (ENNReal.ofReal (2 : ℝ)) (volume.restrict U) := by
    simpa only [ENNReal.ofReal_ofNat] using
      ((memLp_two_iff_integrable_sq hFa.aestronglyMeasurable).2 hF2)
  have hGmem : MemLp G (ENNReal.ofReal (2 : ℝ)) (volume.restrict U) := by
    simpa only [ENNReal.ofReal_ofNat] using
      ((memLp_two_iff_integrable_sq hGb.aestronglyMeasurable).2 hG2)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := F) (g := G) (μ := volume.restrict U)
    Real.HolderConjugate.two_two
    (ae_of_all (volume.restrict U) fun x => Real.sqrt_nonneg _)
    (ae_of_all (volume.restrict U) fun x => Real.sqrt_nonneg _)
    hFmem hGmem
  have hFaSq : (fun x => F x ^ (2 : ℝ)) =
      fun x => matrixFrobeniusNormSq (a x) := by
    funext x
    change Real.sqrt (matrixFrobeniusNormSq (a x)) ^ (2 : ℝ) = _
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hGbSq : (fun x => G x ^ (2 : ℝ)) =
      fun x => matrixFrobeniusNormSq (b x) := by
    funext x
    change Real.sqrt (matrixFrobeniusNormSq (b x)) ^ (2 : ℝ) = _
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hFaSq, hGbSq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  unfold cubeFrobeniusPairingReg cubeFrobeniusMassReg cubeAverage
  have hV : 0 ≤ (cubeVolume Q)⁻¹ := inv_nonneg.mpr (cubeVolume_pos Q).le
  rw [abs_mul, abs_of_nonneg hV, Real.sqrt_mul hV, Real.sqrt_mul hV]
  calc
    (cubeVolume Q)⁻¹ *
        |∫ x in cubeSet Q, ∑ i, ∑ j, a x i j * b x i j ∂volume| ≤
      (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, F x * G x ∂volume :=
        mul_le_mul_of_nonneg_left hstep1 hV
    _ ≤ (cubeVolume Q)⁻¹ *
        (Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume) *
          Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume)) :=
        mul_le_mul_of_nonneg_left hCS hV
    _ = (Real.sqrt (cubeVolume Q)⁻¹ *
          Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume)) *
        (Real.sqrt (cubeVolume Q)⁻¹ *
          Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume)) := by
        calc
          (cubeVolume Q)⁻¹ *
              (Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume) *
                Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume)) =
              (Real.sqrt (cubeVolume Q)⁻¹ * Real.sqrt (cubeVolume Q)⁻¹) *
                (Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (a x) ∂volume) *
                  Real.sqrt (∫ x in cubeSet Q, matrixFrobeniusNormSq (b x) ∂volume)) := by
                rw [Real.mul_self_sqrt hV]
          _ = _ := by ring

end

end Algsuperdiff.Section3.Provider.Stream
