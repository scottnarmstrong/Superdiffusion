import Mathlib
import Algsuperdiff.MainTheorems
import Audit.GeneratorRenormalization.SolutionBasic
import Audit.Support.GeneratorRenormalizationCarrierMeasurability

/-!
# Comparator bridge: `Audit.GeneratorRenormalization` vocabulary → repository

This file connects the statement-audit vocabulary of
`Audit/GeneratorRenormalization/Challenge.lean` (copied verbatim into
`Audit/GeneratorRenormalization/SolutionBasic.lean`, which imports only
Mathlib) to the objects of this repository and of the upstream
`Homogenization` package, so that `Audit/GeneratorRenormalization/Solution.lean`
is literal gluing.

**It is imported by the `Solution` files only.**  The `Challenge` and
`SolutionBasic` files must stay Mathlib-only: a repository import inside the
vocabulary changes instance elaboration there and breaks the comparator's
constant-by-constant closure check.

## Contents

1.  the field-shuffle equivalence `toRepo`/`ofRepo` on the regular
    coefficient-field carrier, and its measurability at the joint σ-algebra;
2.  the two zero-shell coefficient laws and the transport of stationarity,
    `L²` membership, and the law itself along the equivalence;
3.  the induced `Lp` isometry equivalence `lpEquiv`;
4.  the Koopman and coordinate intertwinings, hence the horizontal-gradient
    range, its closure, and the orthogonal projection onto it;
5.  `norm_corrector_eq`, the corrector-norm identity, and the `cstar` tie
    `realizesCstar_iff_cstar_eq`;
6.  the propositional layer: local σ-algebras, triadic cubes, `H¹`/`H¹₀`, the
    Dirichlet predicates, and `Model ↔ ABKModel`;
7.  `exists_sigmaBar_profile_band`, the profile band for the canonical
    `Annealed.sigmaBar M m`, consumed from the repository's frozen induction
    bounds (not reproved here);
8.  the definitional layer, named.

`Audit/Support/AnomalousRegularityBridge.lean` is the same file for the other
challenge's vocabulary; the two differ only in the import, the namespace, the
opened vocabulary namespace, and the last declaration of §14.
-/

namespace Audit.Support.GRBridge

open Algsuperdiff.StatementAudit.GeneratorRenormalization
open MeasureTheory

variable {d : ℕ}

/-! ## 1. The carrier equivalence -/

def toRepo (a : RegCoeffField d) : Homogenization.RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locInt

def ofRepo (a : Homogenization.RegCoeffField d) : RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locInt

theorem ofRepo_toRepo (a : RegCoeffField d) : ofRepo (toRepo a) = a := rfl

theorem toRepo_ofRepo (a : Homogenization.RegCoeffField d) : toRepo (ofRepo a) = a := rfl

theorem isProbeR_iff (φ : Vec d → ℝ) : IsProbeR φ ↔ Homogenization.IsProbeR φ :=
  ⟨fun h => ⟨h.measurable, h.bounded, h.hasCompactSupport⟩,
   fun h => ⟨h.measurable, h.bounded, h.hasCompactSupport⟩⟩

theorem measurable_toRepo : Measurable (toRepo (d := d)) := by
  refine Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_apply_entry y i j
  · intro i j φ hφ
    exact measurable_entryTestR i j ((isProbeR_iff φ).mpr hφ)

theorem measurable_ofRepo : Measurable (ofRepo (d := d)) := by
  refine measurable_into_regCoeffField ?_ ?_
  · intro y i j
    exact Homogenization.measurable_apply_entry y i j
  · intro i j φ hφ
    exact Homogenization.measurable_entryTestR i j ((isProbeR_iff φ).mp hφ)

/-! ## 2. The two zero-shell coefficient laws -/

/-- The challenge-side zero-shell coefficient law. -/
noncomputable abbrev muC (P : ProbabilityMeasure (ShellSeq d)) : Measure (RegCoeffField d) :=
  zeroShellRegMeasure P

/-- The repository-side zero-shell coefficient law. -/
noncomputable abbrev muR (P : ProbabilityMeasure (ShellSeq d)) :
    Measure (Homogenization.RegCoeffField d) :=
  (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw P).toMeasure

theorem measurable_zeroShellRegMap_chal :
    Measurable (fun F : ShellSeq d => ShellField.forgetShell (d := d) (F 0)) :=
  measurable_ofRepo.comp
    (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_zeroShellRegMap (d := d))

theorem map_toRepo_zeroShellRegMeasure (P : ProbabilityMeasure (ShellSeq d)) :
    Measure.map (toRepo (d := d)) (muC P) = muR P :=
  Measure.map_map (μ := P.toMeasure)
    (f := fun F : ShellSeq d => ShellField.forgetShell (d := d) (F 0))
    (g := toRepo (d := d)) measurable_toRepo measurable_zeroShellRegMap_chal

theorem measurePreserving_toRepo (P : ProbabilityMeasure (ShellSeq d)) :
    MeasurePreserving (toRepo (d := d)) (muC P) (muR P) :=
  ⟨measurable_toRepo, map_toRepo_zeroShellRegMeasure P⟩

theorem measurePreserving_ofRepo (P : ProbabilityMeasure (ShellSeq d)) :
    MeasurePreserving (ofRepo (d := d)) (muR P) (muC P) := by
  refine ⟨measurable_ofRepo, ?_⟩
  rw [← map_toRepo_zeroShellRegMeasure P,
    Measure.map_map measurable_ofRepo measurable_toRepo]
  exact Measure.map_id

/-! ## 2b. The definitional intertwinings -/

theorem toRepo_translateReg (z : Vec d) (a : RegCoeffField d) :
    toRepo (translateReg z a) = Homogenization.translateReg z (toRepo a) := rfl

theorem ofRepo_translateReg (z : Vec d) (a : Homogenization.RegCoeffField d) :
    ofRepo (Homogenization.translateReg z a) = translateReg z (ofRepo a) := rfl

theorem toRepo_forgetShell (j : Algsuperdiff.Frozen.Assumptions.ShellField d) :
    toRepo (ShellField.forgetShell j) =
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell j := rfl

theorem originForcing_toRepo (e : Vec d) (a : RegCoeffField d) :
    originForcing e a =
      Algsuperdiff.Frozen.Assumptions.ShellField.originForcing e (toRepo a) := rfl

theorem entryTestR_ofRepo (i j : Fin d) (φ : Vec d → ℝ)
    (a : Homogenization.RegCoeffField d) :
    entryTestR i j φ (ofRepo a) = Homogenization.entryTestR i j φ a := rfl

/-- The challenge's stationarity hypothesis transports to the repository's. -/
theorem repoStationary (P : ProbabilityMeasure (ShellSeq d))
    (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) (muC P) (muC P)) :
    ∀ z : Vec d, Measure.map (Homogenization.translateReg z) (muR P) = muR P := by
  intro z
  calc
    Measure.map (Homogenization.translateReg z) (muR P)
        = Measure.map (Homogenization.translateReg z)
            (Measure.map (toRepo (d := d)) (muC P)) := by
          rw [map_toRepo_zeroShellRegMeasure]
    _ = Measure.map (Homogenization.translateReg z ∘ toRepo (d := d)) (muC P) :=
          Measure.map_map (Homogenization.measurable_translateReg z) measurable_toRepo
    _ = Measure.map (toRepo (d := d) ∘ translateReg z) (muC P) := rfl
    _ = Measure.map (toRepo (d := d)) (Measure.map (translateReg z) (muC P)) :=
          (Measure.map_map measurable_toRepo (measurable_translateReg z)).symm
    _ = Measure.map (toRepo (d := d)) (muC P) := by rw [(hstat z).map_eq]
    _ = muR P := map_toRepo_zeroShellRegMeasure P

/-- The repository's stationarity hypothesis transports to the challenge's. -/
theorem chalStationary (P : ProbabilityMeasure (ShellSeq d))
    (hstat : ∀ z : Vec d, Measure.map (Homogenization.translateReg z) (muR P) = muR P) :
    ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) (muC P) (muC P) := by
  intro z
  refine ⟨measurable_translateReg z, ?_⟩
  have hmapC : Measure.map (ofRepo (d := d)) (muR P) = muC P :=
    (measurePreserving_ofRepo P).map_eq
  calc
    Measure.map (translateReg z) (muC P)
        = Measure.map (translateReg z) (Measure.map (ofRepo (d := d)) (muR P)) := by
          rw [hmapC]
    _ = Measure.map (translateReg z ∘ ofRepo (d := d)) (muR P) :=
          Measure.map_map (measurable_translateReg z) measurable_ofRepo
    _ = Measure.map (ofRepo (d := d) ∘ Homogenization.translateReg z) (muR P) := rfl
    _ = Measure.map (ofRepo (d := d))
            (Measure.map (Homogenization.translateReg z) (muR P)) :=
          (Measure.map_map measurable_ofRepo (Homogenization.measurable_translateReg z)).symm
    _ = Measure.map (ofRepo (d := d)) (muR P) := by rw [hstat z]
    _ = muC P := hmapC

/-- The challenge's `L²` origin-forcing hypothesis transports to the
repository's. -/
theorem repoMemLp (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (hmem : MemLp (originForcing (d := d) e) 2 (muC P)) :
    MemLp (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing (d := d) e) 2 (muR P) := by
  have h := hmem.comp_measurePreserving (measurePreserving_ofRepo P)
  exact h

/-- The repository's `L²` origin-forcing hypothesis transports to the
challenge's. -/
theorem chalMemLp (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (hmem : MemLp (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing (d := d) e) 2
      (muR P)) :
    MemLp (originForcing (d := d) e) 2 (muC P) :=
  hmem.comp_measurePreserving (measurePreserving_toRepo P)

/-! ## 3. The induced `Lp` isometry -/

section LpEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `Lp` isometry induced by the carrier equivalence. -/
noncomputable def lpEquiv (P : ProbabilityMeasure (ShellSeq d)) :
    Lp E 2 (muR P) ≃ₗᵢ[ℝ] Lp E 2 (muC P) where
  toLinearEquiv :=
    { Lp.compMeasurePreservingₗ ℝ (toRepo (d := d)) (measurePreserving_toRepo P) with
      invFun := fun g =>
        Lp.compMeasurePreserving (ofRepo (d := d)) (measurePreserving_ofRepo P) g
      left_inv := by rintro ⟨⟨f⟩, hf⟩; rfl
      right_inv := by rintro ⟨⟨f⟩, hf⟩; rfl }
  norm_map' := fun g => Lp.norm_compMeasurePreserving g (measurePreserving_toRepo P)

theorem lpEquiv_apply (P : ProbabilityMeasure (ShellSeq d)) (g : Lp E 2 (muR P)) :
    lpEquiv P g = Lp.compMeasurePreserving (toRepo (d := d)) (measurePreserving_toRepo P) g :=
  rfl

theorem lpEquiv_toLp (P : ProbabilityMeasure (ShellSeq d)) {g : Homogenization.RegCoeffField d → E}
    (hg : MemLp g 2 (muR P)) :
    lpEquiv P (hg.toLp g) =
      (hg.comp_measurePreserving (measurePreserving_toRepo P)).toLp (g ∘ toRepo (d := d)) :=
  rfl

end LpEquiv

/-! ## 4. Intertwining the Koopman families -/

section Koopman

variable (P : ProbabilityMeasure (ShellSeq d))
  [VAddInvariantMeasure (Homogenization.Vec d) (Homogenization.RegCoeffField d) (muR P)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lpEquiv_koopman
    (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) (muC P) (muC P))
    (z : Vec d) (φ : Lp E 2 (muR P)) :
    lpEquiv P (Algsuperdiff.Probability.Stationary.koopman (μ := muR P) z φ) =
      koopman (μ := muC P) hstat z (lpEquiv P φ) := by
  rcases φ with ⟨⟨f⟩, hf⟩
  rfl

omit [VAddInvariantMeasure (Homogenization.Vec d) (Homogenization.RegCoeffField d) (muR P)] in
theorem lpEquiv_vectorL2Coord (i : Fin d) (F : Lp (HilbertVec d) 2 (muR P)) :
    lpEquiv (E := ℝ) P (Algsuperdiff.Probability.Stationary.vectorL2Coord (μ := muR P) i F) =
      vectorL2Coord (μ := muC P) i (lpEquiv (E := HilbertVec d) P F) := by
  rcases F with ⟨⟨f⟩, hf⟩
  rfl

end Koopman

/-! ## 5. Horizontal gradients, the range, and its closure -/

/-- A linear isometry equivalence transports strong derivatives. -/
theorem hasDerivAt_map {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (e : A ≃ₗᵢ[ℝ] B)
    {f : ℝ → A} {f' : A} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => e (f t)) (e f') x := by
  simpa only [Function.comp_def, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry] using
    (e.toLinearIsometry.toContinuousLinearMap.hasFDerivAt
      (x := f x)).comp_hasDerivAt x h

section Gradients

variable (P : ProbabilityMeasure (ShellSeq d))
  [VAddInvariantMeasure (Homogenization.Vec d) (Homogenization.RegCoeffField d) (muR P)]
  (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) (muC P) (muC P))

theorem hasHorizontalGradient_iff (φ : Lp ℝ 2 (muR P)) (F : Lp (HilbertVec d) 2 (muR P)) :
    Algsuperdiff.Probability.Stationary.HasHorizontalGradient (μ := muR P) φ F ↔
      HasHorizontalGradient (μ := muC P) hstat
        (lpEquiv (E := ℝ) P φ) (lpEquiv (E := HilbertVec d) P F) := by
  constructor
  · intro h i
    have hd := hasDerivAt_map (lpEquiv (E := ℝ) P) (h i)
    simp only [lpEquiv_koopman P hstat, lpEquiv_vectorL2Coord P i F] at hd
    exact hd
  · intro h i
    have hd := hasDerivAt_map (lpEquiv (E := ℝ) P).symm (h i)
    simp only [← lpEquiv_koopman P hstat, ← lpEquiv_vectorL2Coord P i F,
      LinearIsometryEquiv.symm_apply_apply] at hd
    exact hd

/-- The challenge's stationary potential subspace is complete, being a
topological closure inside a complete space. -/
theorem chalPotentialComplete {μ : Measure (RegCoeffField d)}
    (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ) :
    CompleteSpace (stationaryPotentialSubspace (μ := μ) hstat) := by
  change CompleteSpace (horizontalGradientRange (μ := μ) hstat).topologicalClosure
  infer_instance

/-- Hence it carries an orthogonal projection; this is exactly the instance the
challenge's `zeroShellPotentialCorrector` produces by hand. -/
instance chalPotentialHasOrthogonalProjection {μ : Measure (RegCoeffField d)}
    (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ) :
    (stationaryPotentialSubspace (μ := μ) hstat).HasOrthogonalProjection :=
  haveI := chalPotentialComplete hstat
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- A linear isometry equivalence commutes with topological closure of
submodules. -/
theorem map_topologicalClosure {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (e : A ≃ₗᵢ[ℝ] B) (S : Submodule ℝ A) :
    Submodule.map e S.topologicalClosure = (Submodule.map e S).topologicalClosure := by
  refine SetLike.coe_injective ?_
  simp only [Submodule.map_coe, Submodule.topologicalClosure_coe]
  exact e.toHomeomorph.image_closure _

theorem map_horizontalGradientRange :
    Submodule.map (lpEquiv (E := HilbertVec d) P)
        (Algsuperdiff.Probability.Stationary.horizontalGradientRange (μ := muR P) (d := d)) =
      horizontalGradientRange (μ := muC P) hstat := by
  ext F
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨G, hG, rfl⟩
    obtain ⟨ψ, hψ⟩ := hG
    exact ⟨lpEquiv (E := ℝ) P ψ, (hasHorizontalGradient_iff P hstat ψ G).mp hψ⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨(lpEquiv (E := HilbertVec d) P).symm F, ⟨(lpEquiv (E := ℝ) P).symm φ, ?_⟩,
      (lpEquiv (E := HilbertVec d) P).apply_symm_apply F⟩
    rw [hasHorizontalGradient_iff P hstat]
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hφ

theorem map_stationaryPotentialSubspace :
    Submodule.map (lpEquiv (E := HilbertVec d) P)
        (Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
          (μ := muR P) (d := d)) =
      stationaryPotentialSubspace (μ := muC P) hstat := by
  show Submodule.map _ (Submodule.topologicalClosure _) = Submodule.topologicalClosure _
  rw [map_topologicalClosure, map_horizontalGradientRange P hstat]

theorem lpEquiv_starProjection (u : Lp (HilbertVec d) 2 (muR P)) :
    lpEquiv (E := HilbertVec d) P
        ((Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
          (μ := muR P) (d := d)).starProjection u) =
      (stationaryPotentialSubspace (μ := muC P) hstat).starProjection
        (lpEquiv (E := HilbertVec d) P u) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← map_stationaryPotentialSubspace P hstat]
    exact Submodule.mem_map_of_mem (Submodule.starProjection_apply_mem _ u)
  · intro w hw
    rw [← map_stationaryPotentialSubspace P hstat, Submodule.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [← map_sub, LinearIsometryEquiv.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero (K := _) u w' hw'

end Gradients

/-! ## 6. The corrector-norm identity -/

section Corrector

variable (P : ProbabilityMeasure (ShellSeq d))
  (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) (muC P) (muC P))

theorem lpEquiv_corrector (e : Vec d)
    (hmemR : MemLp (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing (d := d) e) 2
      (muR P))
    (hmemC : MemLp (originForcing (d := d) e) 2 (muC P)) :
    lpEquiv (E := HilbertVec d) P
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector P
          (repoStationary P hstat) e hmemR) =
      zeroShellPotentialCorrector P hstat e hmemC := by
  haveI := Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant P
    (repoStationary P hstat)
  have hchal : zeroShellPotentialCorrector P hstat e hmemC =
      -(stationaryPotentialSubspace (μ := muC P) hstat).starProjection
        (hmemC.toLp (originForcing e)) := rfl
  have hrepo : Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector P
        (repoStationary P hstat) e hmemR =
      -(Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
          (μ := muR P) (d := d)).starProjection
        (hmemR.toLp (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing e)) := rfl
  rw [hchal, hrepo, map_neg, lpEquiv_starProjection P hstat]
  rfl

/-- **The deep bridge.**  The challenge's stationary potential corrector and the
repository's have the same `L²` norm. -/
theorem norm_corrector_eq (e : Vec d)
    (hmemR : MemLp (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing (d := d) e) 2
      (muR P))
    (hmemC : MemLp (originForcing (d := d) e) 2 (muC P)) :
    ‖zeroShellPotentialCorrector P hstat e hmemC‖ =
      ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector P
        (repoStationary P hstat) e hmemR‖ := by
  rw [← lpEquiv_corrector P hstat e hmemR hmemC, LinearIsometryEquiv.norm_map]

end Corrector

/-! ## 7. The `cstar` tie -/

section Cstar

/-- The challenge's `RealizesCstar` display and the repository's (J4) display
are the same statement. -/
theorem realizesCstar_iff_raw (P : ProbabilityMeasure (ShellSeq d))
    (hstationary : ∀ z : Vec d,
      Measure.map (Algsuperdiff.Frozen.Assumptions.ShellField.translate z)
          (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure =
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw P).toMeasure)
    (htail : ∀ t : ℝ, 1 ≤ t →
      P.toMeasure {F | t < Algsuperdiff.Frozen.Assumptions.ShellField.j2Observable d (F 0)} ≤
        ENNReal.ofReal (Real.exp (-(t ^ 2))))
    (c : ℝ) :
    RealizesCstar d P c ↔
      ∀ e : {e : Vec d // Homogenization.Book.Ch02.vecNorm e = 1},
        ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector P
            (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
              P hstationary)
            e.1 (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
              P htail e.1 e.2)‖ ^ 2 =
          c * Real.log 3 := by
  rw [realizesCstar_iff_corrector P c]
  have hstatR :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      P hstationary
  have hstatC := chalStationary P hstatR
  constructor
  · intro h e
    have hmemR := Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
      P htail e.1 e.2
    have hmemC := chalMemLp P e.1 hmemR
    have hgoal :
        ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector P hstatR e.1
            hmemR‖ =
          ‖zeroShellPotentialCorrector P hstatC e.1 hmemC‖ :=
      (norm_corrector_eq P hstatC e.1 hmemR hmemC).symm
    rw [hgoal]
    exact h hstatC e.1 e.2 hmemC
  · intro h hstat' e he hmem'
    have hmemR := Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
      P htail e he
    rw [norm_corrector_eq P hstat' e hmemR hmem']
    exact h ⟨e, he⟩

/-- The model form of `realizesCstar_iff_raw`. -/
theorem realizesCstar_iff (M : Algsuperdiff.Section3.ABKModel d) (c : ℝ) :
    RealizesCstar d M.P c ↔
      ∀ e : {e : Vec d // Homogenization.Book.Ch02.vecNorm e = 1},
        ‖Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellPotentialCorrector M.P
            (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
              M.P M.J1.stationary)
            e.1
            (Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
              M.P M.J2.gaussian_tail e.1 e.2)‖ ^ 2 =
          c * Real.log 3 :=
  realizesCstar_iff_raw M.P M.J1.stationary M.J2.gaussian_tail c

/-- The canonical `cstar` realizes the challenge display. -/
theorem realizesCstar_cstar (M : Algsuperdiff.Section3.ABKModel d) :
    RealizesCstar d M.P (Algsuperdiff.Section3.Disorder.cstar M) :=
  (realizesCstar_iff M _).mpr (Algsuperdiff.Section3.Disorder.cstar_characterization M).2.1

/-- **The `cstar` tie.**  A positive constant realizes the challenge's corrector
energy display exactly when it is the repository's canonical `cstar`. -/
theorem realizesCstar_iff_cstar_eq (M : Algsuperdiff.Section3.ABKModel d) {c : ℝ}
    (hc : 0 < c) :
    RealizesCstar d M.P c ↔ Algsuperdiff.Section3.Disorder.cstar M = c := by
  constructor
  · intro h
    exact ((Algsuperdiff.Section3.Disorder.cstar_characterization M).2.2 c hc
      ((realizesCstar_iff M c).mp h)).symm
  · rintro rfl
    exact realizesCstar_cstar M

end Cstar

/-! ## 8. The local σ-algebras -/

theorem comap_ofRepo_localSigmaR (U : Set (Vec d)) :
    MeasurableSpace.comap (ofRepo (d := d)) (LocalSigmaR U) = Homogenization.LocalSigmaR U := by
  rw [LocalSigmaR, Homogenization.LocalSigmaR, MeasurableSpace.comap_generateFrom]
  congr 1
  ext s
  constructor
  · rintro ⟨t, ⟨i, j, φ, hφ, hsupp, r, hr, rfl⟩, rfl⟩
    exact ⟨i, j, φ, (isProbeR_iff φ).mp hφ, hsupp, r, hr, rfl⟩
  · rintro ⟨i, j, φ, hφ, hsupp, r, hr, rfl⟩
    exact ⟨entryTestR i j φ ⁻¹' r,
      ⟨i, j, φ, (isProbeR_iff φ).mpr hφ, hsupp, r, hr, rfl⟩, rfl⟩

theorem lihLocalSigma_eq (U : Set (Vec d)) :
    lihLocalSigma U = Algsuperdiff.Frozen.Assumptions.ShellField.lihLocalSigma U := by
  rw [lihLocalSigma, Algsuperdiff.Frozen.Assumptions.ShellField.lihLocalSigma,
    ← comap_ofRepo_localSigmaR U, MeasurableSpace.comap_comp]
  rfl

/-! ## 9. Triadic cubes -/

def toRepoCube (Q : TriadicCube d) : Homogenization.TriadicCube d where
  scale := Q.scale
  index := Q.index

def ofRepoCube (Q : Homogenization.TriadicCube d) : TriadicCube d where
  scale := Q.scale
  index := Q.index

theorem ofRepoCube_toRepoCube (Q : TriadicCube d) : ofRepoCube (toRepoCube Q) = Q := rfl

theorem toRepoCube_ofRepoCube (Q : Homogenization.TriadicCube d) :
    toRepoCube (ofRepoCube Q) = Q := rfl

theorem openCubeSet_toRepoCube (Q : TriadicCube d) :
    openCubeSet Q = Homogenization.openCubeSet (toRepoCube Q) := rfl

theorem toRepoCube_originCube (m : ℤ) :
    toRepoCube (originCube d m) = Homogenization.originCube d m := rfl

theorem openCubeSet_originCube (m : ℤ) :
    openCubeSet (originCube d m) =
      Homogenization.openCubeSet (Homogenization.originCube d m) := rfl

/-! ## 10. Sobolev structure copies -/

section Sobolev

variable {U : Set (Vec d)}

def toRepoH1 (u : H1Function U) : Homogenization.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

def ofRepoH1 (u : Homogenization.H1Function U) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

theorem ofRepoH1_toRepoH1 (u : H1Function U) : ofRepoH1 (toRepoH1 u) = u := rfl

theorem toRepoH1_ofRepoH1 (u : Homogenization.H1Function U) : toRepoH1 (ofRepoH1 u) = u := rfl

def toRepoH10 (u : H10Function U) : Homogenization.H10Function U where
  toH1Function := toRepoH1 u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

def ofRepoH10 (u : Homogenization.H10Function U) : H10Function U where
  toH1Function := ofRepoH1 u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

theorem ofRepoH10_toRepoH10 (u : H10Function U) : ofRepoH10 (toRepoH10 u) = u := rfl

theorem toRepoH10_ofRepoH10 (u : Homogenization.H10Function U) :
    toRepoH10 (ofRepoH10 u) = u := rfl

end Sobolev

/-! ## 11. The Dirichlet problem -/

section Dirichlet

variable (a : Vec d → Mat d) (W : Set (Vec d)) (g : Vec d → Vec d)

/-- The two divergence-form weak-solution predicates agree; the test-function
quantifier is transported in both directions by `toRepoH10`/`ofRepoH10`. -/
theorem isDivFormWeakSolutionOn_iff (u : H1Function W) :
    IsDivFormWeakSolutionOn a W u g ↔
      Algsuperdiff.Section4.Support.IsDivFormWeakSolutionOn a W (toRepoH1 u) g :=
  ⟨fun h φ => h (ofRepoH10 φ), fun h φ => h (toRepoH10 φ)⟩

theorem hasZeroTraceDifferenceOn_iff (u h : H1Function W) :
    HasZeroTraceDifferenceOn W u h ↔
      Algsuperdiff.Section4.Support.HasZeroTraceDifferenceOn W (toRepoH1 u) (toRepoH1 h) :=
  ⟨fun ⟨w, hv, hg⟩ => ⟨toRepoH10 w, hv, hg⟩, fun ⟨w, hv, hg⟩ => ⟨ofRepoH10 w, hv, hg⟩⟩

theorem isDirichletSolutionOn_iff (Q : TriadicCube d)
    (u h : H1Function (openCubeSet Q)) :
    IsDirichletSolutionOn a Q u h g ↔
      Algsuperdiff.Section4.Support.IsDirichletSolutionOn a (toRepoCube Q)
        (toRepoH1 u) (toRepoH1 h) g :=
  and_congr (hasZeroTraceDifferenceOn_iff _ u h) (isDivFormWeakSolutionOn_iff a _ g u)

end Dirichlet

/-! ## 12. The standing model -/

section ShellFieldExt
open scoped Matrix.Norms.Elementwise

/-- **Shell-field extensionality.**  A `ShellField` is determined by its value
function: the stored first and second derivatives are pinned by
`HasFDerivAt.unique`.  This is the uniqueness half of the presentation delta
that replaces the constructed shell transformations by pointwise-characterized
quantified maps, so that the quantified `Model` fields are *equivalent* to the
fields that named the canonical maps. -/
theorem shellField_ext {j k : ShellField d} (h : ∀ x, j x = k x) : j = k := by
  have h1 : j.1.1 = k.1.1 := by
    ext x i l
    exact congrFun (congrFun (h x) i) l
  have h2 : j.1.2.1 = k.1.2.1 := by
    refine ContinuousMap.ext fun x => ?_
    refine (j.2.1 x).unique ?_
    rw [h1]
    exact k.2.1 x
  have h3 : j.1.2.2 = k.1.2.2 := by
    refine ContinuousMap.ext fun x => ?_
    refine (j.2.2.1 x).unique ?_
    rw [h2]
    exact k.2.2.1 x
  exact Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))

/-- Sequence-level shell extensionality. -/
theorem shellSeq_ext {F G : ShellSeq d} (h : ∀ k x, F k x = G k x) : F = G :=
  funext fun k => shellField_ext (h k)

end ShellFieldExt

/-- The challenge model's stationarity field, instantiated at the canonical
translation. -/
theorem modelStationary (m : Model d) : ∀ z : Vec d,
    Measure.map (Algsuperdiff.Frozen.Assumptions.ShellField.translate z)
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw m.P).toMeasure =
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw m.P).toMeasure :=
  fun z => m.stationary z (Algsuperdiff.Frozen.Assumptions.ShellField.translate z)
    (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_translate z) (fun _ _ => rfl)

/-- The challenge's flat `Model` is the repository's `ABKModel`. -/
def toABKModel (m : Model d) : Algsuperdiff.Section3.ABKModel d where
  nu := m.nu
  nu_pos := m.nu_pos
  gamma := m.gamma
  P := m.P
  shellPrefix :=
    { dimension := m.dimension
      gamma_pos := m.gamma_pos
      gamma_le_quarter := m.gamma_le_quarter
      independent := m.independent
      marginal_scaling := fun k =>
        m.marginal_scaling k (Algsuperdiff.Frozen.Assumptions.ShellField.triadicScale m.gamma k)
          (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_triadicScale m.gamma k) (fun _ _ => rfl) }
  J1 :=
    { integrable := m.integrable
      mean_zero := m.mean_zero
      stationary := modelStationary m
      range_dependence := by
        intro U V hU hV hsep
        have h := m.range_dependence U V hU hV hsep
        rwa [lihLocalSigma_eq, lihLocalSigma_eq] at h }
  J2 := { gaussian_tail := m.gaussian_tail }
  J3 :=
    { hyperoctahedral := fun R hR =>
        m.hyperoctahedral R hR (Algsuperdiff.Frozen.Assumptions.ShellField.rotateSequence R hR)
          (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_rotateSequence R hR) (fun _ _ _ => rfl)
      negation :=
        m.negation Algsuperdiff.Frozen.Assumptions.ShellField.negateSequence Algsuperdiff.Frozen.Assumptions.ShellField.measurable_negateSequence
          (fun _ _ _ => neg_one_smul ℝ _) }
  J4 :=
    { nondegenerate := by
        obtain ⟨c, hc, hrealizes⟩ := m.nondegenerate
        exact ⟨c, hc,
          (realizesCstar_iff_raw m.P (modelStationary m) m.gaussian_tail c).mp hrealizes⟩ }

theorem toABKModel_P (m : Model d) : (toABKModel m).P = m.P := rfl

theorem toABKModel_nu (m : Model d) : (toABKModel m).nu = m.nu := rfl

theorem toABKModel_gamma (m : Model d) : (toABKModel m).gamma = m.gamma := rfl

/-- The repository's `ABKModel` is the challenge's flat `Model`. -/
def ofABKModel (M : Algsuperdiff.Section3.ABKModel d) : Model d where
  nu := M.nu
  nu_pos := M.nu_pos
  gamma := M.gamma
  P := M.P
  dimension := M.shellPrefix.dimension
  gamma_pos := M.shellPrefix.gamma_pos
  gamma_le_quarter := M.shellPrefix.gamma_le_quarter
  independent := M.shellPrefix.independent
  marginal_scaling := by
    intro k T hT hchar
    have : T = Algsuperdiff.Frozen.Assumptions.ShellField.triadicScale M.gamma k :=
      funext fun j => shellField_ext fun x => hchar j x
    subst this
    exact M.shellPrefix.marginal_scaling k
  integrable := M.J1.integrable
  mean_zero := M.J1.mean_zero
  stationary := by
    intro z T _ hchar
    have : T = Algsuperdiff.Frozen.Assumptions.ShellField.translate z :=
      funext fun j => shellField_ext fun x => hchar j x
    subst this
    exact M.J1.stationary z
  range_dependence := by
    intro U V hU hV hsep
    have h := M.J1.range_dependence U V hU hV hsep
    rwa [← lihLocalSigma_eq, ← lihLocalSigma_eq] at h
  gaussian_tail := M.J2.gaussian_tail
  hyperoctahedral := by
    intro R hR T hT hchar
    have : T = Algsuperdiff.Frozen.Assumptions.ShellField.rotateSequence R hR :=
      funext fun F => shellSeq_ext fun k x => hchar F k x
    subst this
    exact M.J3.hyperoctahedral R hR
  negation := by
    intro T hT hchar
    have : T = Algsuperdiff.Frozen.Assumptions.ShellField.negateSequence :=
      funext fun F => shellSeq_ext fun k x => by
        rw [hchar F k x]; exact (neg_one_smul ℝ _).symm
    subst this
    exact M.J3.negation
  nondegenerate := by
    obtain ⟨c, hc, hdisplay⟩ := M.J4.nondegenerate
    exact ⟨c, hc, (realizesCstar_iff_raw M.P M.J1.stationary M.J2.gaussian_tail c).mpr hdisplay⟩

/-- The `cstar` of the transported model realizes the challenge display. -/
theorem realizesCstar_cstar_toABKModel (m : Model d) :
    RealizesCstar d m.P (Algsuperdiff.Section3.Disorder.cstar (toABKModel m)) :=
  realizesCstar_cstar (toABKModel m)

/-! ## 13. The `sigmaBar` profile band for the canonical scalar

Consumed, not reproved: the repository's frozen induction bounds already give
Theorem B's profile band for the canonical `Annealed.sigmaBar M m`. -/

theorem exists_sigmaBar_profile_band (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : Algsuperdiff.Section3.ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Algsuperdiff.Section3.Disorder.cstar M) ^ 10 →
        ∀ m : ℤ,
          0 < (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) ∧
          |(Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) -
              Real.sqrt (M.nu ^ 2 +
                Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))| ≤
            C * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ^ 2 *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) := by
  obtain ⟨C, hC, hbounds⟩ := Algsuperdiff.Frozen.Section3.induction_bounds d
  exact ⟨C, hC, fun M hgamma m =>
    ⟨(Algsuperdiff.Section3.Annealed.sigmaBar M m).2, (hbounds M hgamma).2 m⟩⟩

/-! ## 14. The definitional layer, named

Every bridge below is `rfl`; they are named so that the `Solution` assembly is
literal gluing rather than a search for the right `show`. -/

theorem shellField_eq (d : ℕ) :
    ShellField d = Algsuperdiff.Frozen.Assumptions.ShellField d := rfl

theorem shellFieldTopologicalSpace_eq (d : ℕ) :
    shellFieldTopologicalSpace d =
      Algsuperdiff.Frozen.Assumptions.shellFieldCompactOpenTopology d := rfl

theorem shellFieldMeasurableSpace_eq (d : ℕ) :
    shellFieldMeasurableSpace d =
      Algsuperdiff.Frozen.Assumptions.shellFieldBorelMeasurableSpace d := rfl

theorem j2Observable_eq (d : ℕ) :
    j2Observable d = Algsuperdiff.Frozen.Assumptions.ShellField.j2Observable d := rfl

theorem lowerTailGood_eq :
    LowerTailGood (d := d) = Algsuperdiff.Section3.Cutoff.LowerTailGood (d := d) := rfl

theorem cutoffSample_eq (d : ℕ) :
    CutoffSample d = Algsuperdiff.Section3.Cutoff.CutoffSample d := rfl

theorem cutoffSampleMeasure_eq (M : Algsuperdiff.Section3.ABKModel d) :
    cutoffSampleMeasure M.P = (Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure := rfl

theorem cutoffSampleMeasure_toABKModel (m : Model d) :
    cutoffSampleMeasure m.P =
      (Algsuperdiff.Section3.Cutoff.cutoffSampleLaw (toABKModel m)).toMeasure := rfl

theorem coefficientCutoff_eq (nu : ℝ) (L : ℤ)
    (omega : Algsuperdiff.Section3.Cutoff.CutoffSample d) :
    coefficientCutoff nu L omega =
      (Algsuperdiff.Section3.Cutoff.coefficientCutoff nu L omega).toCoeffField := rfl

theorem vecNorm_eq : vecNorm (d := d) = Homogenization.Book.Ch02.vecNorm (d := d) := rfl

theorem vecNormSq_eq : vecNormSq (d := d) = Homogenization.vecNormSq (d := d) := rfl

theorem vecDot_eq : vecDot (d := d) = Homogenization.vecDot (d := d) := rfl

theorem matVecMul_eq : matVecMul (d := d) = Homogenization.matVecMul (d := d) := rfl

theorem basisVec_eq : basisVec (d := d) = Homogenization.basisVec (d := d) := rfl

theorem isSignedPermutationMatrix_eq (R : Mat d) :
    IsSignedPermutationMatrix R = Homogenization.IsSignedPermutationMatrix R := rfl

theorem slopeCLM_eq : slopeCLM (d := d) = Algsuperdiff.Section4.Support.slopeCLM (d := d) := rfl

theorem hasGradientOn_eq :
    HasGradientOn (d := d) = Algsuperdiff.Section4.Support.HasGradientOn (d := d) := rfl

theorem holderSeminormBoundOn_eq {E : Type*} [NormedAddCommGroup E] :
    HolderSeminormBoundOn (d := d) (E := E) =
      Algsuperdiff.Section4.Support.HolderSeminormBoundOn (d := d) (E := E) := rfl

theorem memL2On_eq (U : Set (Vec d)) : MemL2On U = Homogenization.MemL2On U := rfl

theorem gradMemL2On_eq (U : Set (Vec d)) : GradMemL2On U = Homogenization.GradMemL2On U := rfl

theorem hasWeakGradientOn_eq (U : Set (Vec d)) :
    HasWeakGradientOn U = Homogenization.HasWeakGradientOn U := rfl

theorem volumeAverage_eq : volumeAverage (d := d) = Homogenization.volumeAverage (d := d) := rfl

end Audit.Support.GRBridge
