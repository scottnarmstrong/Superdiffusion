import Algsuperdiff.Section3.Provider.Stream.IncrementLpGain

/-!
# A local measurable representative for entrywise square mass

This module supplies deterministic infrastructure for the diagonal leg of the
corrected `e.km.kn.L2.bound` argument.  The existing countably generated
`regFieldLpMassRep` is composed with a one-entry projection of a regular matrix
field.  Its operator-norm square is then exactly the square of that entry.

The resulting observable is measurable in the local restriction sigma algebra,
translation covariant, and agrees on continuous fields with the literal cube
average of the squared entry.  These facts let the finite-range partition
theorem be applied entry by entry without adding any premise to a later
source-facing declaration.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open Homogenization
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The regular matrix field obtained by retaining exactly one scalar entry. -/
def entryProjectionReg (i j : Fin d) (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x r s => if r = i ∧ s = j then a x i j else 0
  entry_measurable := by
    intro r s
    by_cases h : r = i ∧ s = j
    · simpa [h] using a.entry_measurable i j
    · simp [h]
  entry_locInt := by
    intro r s
    by_cases h : r = i ∧ s = j
    · simpa [h] using a.entry_locInt i j
    · simpa [h] using
        (MeasureTheory.locallyIntegrable_const (0 : ℝ) :
          LocallyIntegrable (fun _ : Vec d => (0 : ℝ)) volume)

@[simp] theorem entryProjectionReg_apply (i j : Fin d) (a : RegCoeffField d)
    (x : Vec d) (r s : Fin d) :
    entryProjectionReg i j a x r s = if r = i ∧ s = j then a x i j else 0 :=
  rfl

/-- The projection commutes with spatial translation. -/
theorem entryProjectionReg_translateReg (i j : Fin d) (z : Vec d)
    (a : RegCoeffField d) :
    entryProjectionReg i j (translateReg z a) =
      translateReg z (entryProjectionReg i j a) := by
  ext x r s
  simp [entryProjectionReg_apply, translateReg_apply]

/-- The projection commutes with spatial dilation. -/
theorem entryProjectionReg_smulReg (i j : Fin d) {r : ℝ} (hr : r ≠ 0)
    (a : RegCoeffField d) :
    entryProjectionReg i j (smulReg r hr a) =
      smulReg r hr (entryProjectionReg i j a) := by
  ext x p q
  simp [entryProjectionReg_apply, smulReg_apply]

/-- A one-entry matrix has operator norm equal to the absolute value of its
retained entry. -/
theorem matrixOperatorNorm_entryProjectionReg (i j : Fin d)
    (a : RegCoeffField d) (x : Vec d) :
    Book.Ch02.matrixOperatorNorm (entryProjectionReg i j a x) = |a x i j| := by
  apply le_antisymm
  · refine (matrixOperatorNorm_le_sum_univ_abs_entry
      (entryProjectionReg i j a x)).trans_eq ?_
    classical
    rw [Fintype.sum_prod_type]
    simp only [entryProjectionReg_apply]
    calc
      (∑ r : Fin d, ∑ s : Fin d,
          |if r = i ∧ s = j then a x i j else 0|) =
          ∑ r : Fin d, if r = i then |a x i j| else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : r = i
        · subst r
          rw [Finset.sum_eq_single j]
          · simp
          · intro s _ hsj
            simp [hsj]
          · simp
        · simp [hr]
      _ = |a x i j| := by simp
  · simpa [entryProjectionReg_apply] using
      (Book.Ch02.abs_entry_le_matrixOperatorNorm
        (entryProjectionReg i j a x) i j)

/-- The entry projection is measurable from a local carrier sigma algebra to
the same local carrier sigma algebra. -/
theorem measurable_entryProjectionReg_localSigmaR (U : Set (Vec d)) (i j : Fin d) :
    @Measurable (RegCoeffField d) (RegCoeffField d)
      (LocalSigmaR U) (LocalSigmaR U) (entryProjectionReg i j) := by
  letI : MeasurableSpace (RegCoeffField d) := LocalSigmaR U
  refine measurable_generateFrom ?_
  rintro _ ⟨r, s, phi, hphi, hsupp, t, ht, rfl⟩
  have hbase : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
      (entryTestR i j phi) :=
    measurable_entryTestR_localSigmaR i j hphi hsupp
  by_cases h : r = i ∧ s = j
  · rcases h with ⟨rfl, rfl⟩
    have heq : (fun a : RegCoeffField d =>
        entryTestR r s phi (entryProjectionReg r s a)) = entryTestR r s phi := by
      funext a
      unfold entryTestR
      congr 1
      funext x
      simp [entryProjectionReg_apply]
    change MeasurableSet
      ((fun a : RegCoeffField d =>
        entryTestR r s phi (entryProjectionReg r s a)) ⁻¹' t)
    rw [heq]
    exact hbase ht
  · have heq : (fun a : RegCoeffField d =>
        entryTestR r s phi (entryProjectionReg i j a)) = fun _ => 0 := by
      funext a
      unfold entryTestR
      simp [entryProjectionReg_apply, h]
    change MeasurableSet
      ((fun a : RegCoeffField d =>
        entryTestR r s phi (entryProjectionReg i j a)) ⁻¹' t)
    rw [heq]
    exact measurable_const ht

/-- The countably generated local representative of the squared `(i,j)` entry
mass on a set. -/
def regFieldEntrySqMassRep (i j : Fin d) (U : Set (Vec d))
    (a : RegCoeffField d) : ℝ :=
  |regFieldLpMassRep 2 U (entryProjectionReg i j a)|

theorem measurable_regFieldEntrySqMassRep_localSigmaR (U : Set (Vec d))
    (i j : Fin d) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
      (regFieldEntrySqMassRep i j U) :=
  continuous_abs.measurable.comp
    ((measurable_regFieldLpMassRep_localSigmaR 2 U).comp
      (measurable_entryProjectionReg_localSigmaR U i j))

theorem measurable_regFieldEntrySqMassRep (U : Set (Vec d)) (i j : Fin d) :
    Measurable (regFieldEntrySqMassRep i j U) :=
  (measurable_regFieldEntrySqMassRep_localSigmaR U i j).mono
    (LocalSigmaR_le U) le_rfl

theorem isLocalRandomVariable_regFieldEntrySqMassRep {U : Set (Vec d)}
    (hU : MeasurableSet U) (i j : Fin d) :
    Book.Ch04.IsRestrictionLocalRandomVariable U hU
      (regFieldEntrySqMassRep i j U) :=
  measurable_restrictionSigmaR_of_measurable_localSigmaR hU
    (measurable_regFieldEntrySqMassRep_localSigmaR U i j)

/-- Translation covariance of the entry-square representative. -/
theorem isTranslationCovariantR_regFieldEntrySqMassRep (i j : Fin d) :
    Book.Ch04.IsRestrictionTranslationCovariant
      (regFieldEntrySqMassRep (d := d) i j) := by
  intro U z a
  unfold regFieldEntrySqMassRep
  rw [entryProjectionReg_translateReg,
    isTranslationCovariantR_regFieldLpMassRep 2 U z
      (entryProjectionReg i j a)]

theorem regFieldEntrySqMassRep_nonneg (i j : Fin d) (U : Set (Vec d))
    (a : RegCoeffField d) : 0 ≤ regFieldEntrySqMassRep i j U a :=
  abs_nonneg _

/-- On a continuous regular field, the representative is the literal cube
average of the squared retained entry. -/
theorem regFieldEntrySqMassRep_cubeSet_eq_cubeAverage (i j : Fin d)
    (Q : TriadicCube d) (a : RegCoeffField d)
    (hcont : ∀ r s, Continuous fun x : Vec d => a x r s) :
    regFieldEntrySqMassRep i j (cubeSet Q) a =
      cubeAverage Q (fun x => (a x i j) ^ 2) := by
  have hproj : ∀ r s,
      Continuous fun x : Vec d => entryProjectionReg i j a x r s := by
    intro r s
    by_cases h : r = i ∧ s = j
    · simpa [entryProjectionReg_apply, h] using hcont i j
    · simpa [entryProjectionReg_apply, h] using
        (continuous_const : Continuous fun _ : Vec d => (0 : ℝ))
  rw [regFieldEntrySqMassRep,
    regFieldLpMassRep_cubeSet_eq_regFieldLpMass_of_continuous (by norm_num) Q hproj]
  rw [abs_of_nonneg]
  · rw [
    regFieldLpMass, cubeAverage, volume_cubeSet_toReal]
    refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
    apply setIntegral_congr_fun (measurableSet_cubeSet Q)
    intro x _
    change Book.Ch02.matrixOperatorNorm (entryProjectionReg i j a x) ^ 2 =
      (a x i j) ^ 2
    rw [matrixOperatorNorm_entryProjectionReg, Real.rpow_two, sq_abs]
  · unfold regFieldLpMass
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x => Real.rpow_nonneg
        (Book.Ch02.matrixOperatorNorm_nonneg _) 2)

/-- Reading the representative at a dilated continuous field is the entry-square
average on the correspondingly dilated cube. -/
theorem regFieldEntrySqMassRep_cubeSet_smulReg_eq_cubeAverage (i j : Fin d)
    (s : ℤ) {r : ℝ} (hr : r ≠ 0) (hrs : r = (3 : ℝ) ^ s)
    (Q : TriadicCube d) (a : RegCoeffField d)
    (hcont : ∀ p q, Continuous fun x : Vec d => a x p q) :
    regFieldEntrySqMassRep i j (cubeSet Q) (smulReg r hr a) =
      cubeAverage (dilateCube s Q) (fun x => (a x i j) ^ 2) := by
  have hrpos : 0 < r := by rw [hrs]; exact zpow_pos (by norm_num) s
  have hproj : ∀ p q,
      Continuous fun x : Vec d => entryProjectionReg i j a x p q := by
    intro p q
    by_cases h : p = i ∧ q = j
    · simpa [entryProjectionReg_apply, h] using hcont i j
    · simpa [entryProjectionReg_apply, h] using
        (continuous_const : Continuous fun _ : Vec d => (0 : ℝ))
  rw [regFieldEntrySqMassRep, entryProjectionReg_smulReg,
    regFieldLpMassRep_cubeSet_eq_regFieldLpMass_of_continuous (by norm_num) Q]
  · rw [abs_of_nonneg]
    · rw [regFieldLpMass_smulReg 2 hr hrpos, hrs, ← cubeSet_dilateCube,
      regFieldLpMass, cubeAverage, volume_cubeSet_toReal]
      refine congrArg (fun t : ℝ => (cubeVolume (dilateCube s Q))⁻¹ * t) ?_
      apply setIntegral_congr_fun (measurableSet_cubeSet (dilateCube s Q))
      intro x _
      change Book.Ch02.matrixOperatorNorm (entryProjectionReg i j a x) ^ 2 =
        (a x i j) ^ 2
      rw [matrixOperatorNorm_entryProjectionReg, Real.rpow_two, sq_abs]
    · unfold regFieldLpMass
      exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
        (integral_nonneg fun x => Real.rpow_nonneg
          (Book.Ch02.matrixOperatorNorm_nonneg _) 2)
  · intro p q
    exact (hproj p q).comp (continuous_const_smul r)

end

end Algsuperdiff.Section3.Provider.Stream
