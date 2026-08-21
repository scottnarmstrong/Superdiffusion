import Mathlib
import Audit.GeneratorRenormalization.SolutionBasic

/-!
# Carrier measurability for the `GeneratorRenormalization` audit vocabulary

Mathlib-only (like the vocabulary itself): these are the measurability facts the
challenge used to prove inline.  The challenge now universally quantifies over
`MeasurePreserving (translateReg z)` proofs — the author-approved proof-argument
shape — so the obligations are discharged here, on the solution side.

This module deliberately imports **only** Mathlib and the vocabulary copy: the
proofs below are sensitive to which `MeasurableSpace` instance is found for
`Vec d → Mat d`, and a repository import introduces a competing one.
-/

namespace Algsuperdiff
namespace StatementAudit
namespace GeneratorRenormalization

open MeasureTheory

noncomputable section

theorem IsProbeR.comp_homeomorph {d : ℕ} {φ : Vec d → ℝ} (hφ : IsProbeR φ)
    (h : Vec d ≃ₜ Vec d) : IsProbeR (φ ∘ h) := by
  obtain ⟨C, hC⟩ := hφ.bounded
  exact ⟨hφ.measurable.comp h.continuous.measurable, ⟨C, fun x => hC (h x)⟩,
    hφ.hasCompactSupport.comp_homeomorph h⟩

section RegCoeffFieldMeasurability
variable {d : ℕ}
theorem measurable_into_sup {α β : Type*} {dom : MeasurableSpace α}
    {m1 m2 : MeasurableSpace β} {f : α → β}
    (h1 : @Measurable α β dom m1 f) (h2 : @Measurable α β dom m2 f) :
    @Measurable α β dom (m1 ⊔ m2) f := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_sup]
  exact sup_le h1.comap_le h2.comap_le

theorem measurable_matrix_of_entries {α : Type*} [MeasurableSpace α]
    {h : α → Mat d} (H : ∀ i j, Measurable (fun a => h a i j)) : Measurable h :=
  measurable_pi_lambda h (fun i => measurable_pi_lambda _ (fun j => H i j))
theorem measurable_toFun_of_entries {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d}
    (H : ∀ (y : Vec d) (i j : Fin d), Measurable (fun a => F a y i j)) :
    @Measurable α (Vec d → Mat d) _ MeasurableSpace.pi (fun a => (F a).toFun) :=
  measurable_pi_lambda _ (fun y => measurable_matrix_of_entries (fun i j => H y i j))

theorem measurable_into_pointwiseSigmaR {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d}
    (h : @Measurable α (Vec d → Mat d) _ MeasurableSpace.pi (fun a => (F a).toFun)) :
    @Measurable α (RegCoeffField d) _ (pointwiseSigmaR d) F := by
  rw [measurable_iff_comap_le, pointwiseSigmaR, MeasurableSpace.comap_comp]
  exact h.comap_le

theorem measurable_into_entryTestSigmaR {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d}
    (h : ∀ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ →
      Measurable (fun a => entryTestR i j φ (F a))) :
    @Measurable α (RegCoeffField d) _ (entryTestSigmaR d) F := by
  refine measurable_generateFrom ?_
  rintro s ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h i j φ hφ ht

theorem measurable_into_regCoeffField {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d}
    (hpt : ∀ (y : Vec d) (i j : Fin d), Measurable (fun a => F a y i j))
    (hgen : ∀ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ →
      Measurable (fun a => entryTestR i j φ (F a))) :
    Measurable F :=
  measurable_into_sup
    (measurable_into_pointwiseSigmaR (measurable_toFun_of_entries hpt))
    (measurable_into_entryTestSigmaR hgen)

theorem measurable_apply_entry (y : Vec d) (i j : Fin d) :
    Measurable (fun a : RegCoeffField d => a y i j) := by
  have htoFun : @Measurable (RegCoeffField d) (Vec d → Mat d) (pointwiseSigmaR d)
      MeasurableSpace.pi RegCoeffField.toFun := Measurable.of_comap_le le_rfl
  have hentry : Measurable (fun f : Vec d → Mat d => f y i j) :=
    ((measurable_pi_apply y).eval).eval
  exact (hentry.comp htoFun).mono le_sup_left le_rfl

theorem measurable_entryTestR (i j : Fin d) {φ : Vec d → ℝ} (hφ : IsProbeR φ) :
    Measurable (entryTestR i j φ) := by
  have h : @Measurable (RegCoeffField d) ℝ (entryTestSigmaR d) _ (entryTestR i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h.mono le_sup_right le_rfl

end RegCoeffFieldMeasurability

theorem entryTestR_translateReg {d : ℕ} (i j : Fin d) (φ : Vec d → ℝ) (z : Vec d)
    (a : RegCoeffField d) :
    entryTestR i j φ (translateReg z a) = entryTestR i j (fun y => φ (y - z)) a := by
  unfold entryTestR
  have hcomp := (measurePreserving_add_right (volume : Measure (Vec d)) z).integral_comp
    (Homeomorph.addRight z).measurableEmbedding (fun y => a y i j * φ (y - z))
  rw [← hcomp]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [add_sub_cancel_right]
  rfl

theorem measurable_translateReg {d : ℕ} (z : Vec d) :
    Measurable (translateReg (d := d) z) := by
  refine measurable_into_regCoeffField ?_ ?_
  · intro y i j
    have hfun : (fun a : RegCoeffField d => translateReg z a y i j)
        = fun a => a (y + z) i j := rfl
    rw [hfun]
    exact measurable_apply_entry (y + z) i j
  · intro i j φ hφ
    have hfun : (fun a : RegCoeffField d => entryTestR i j φ (translateReg z a))
        = fun a => entryTestR i j (fun y => φ (y - z)) a :=
      funext fun a => entryTestR_translateReg i j φ z a
    rw [hfun]
    refine measurable_entryTestR i j ?_
    have hprobe := hφ.comp_homeomorph (Homeomorph.subRight z)
    simpa only [Function.comp_def, Homeomorph.subRight_apply] using hprobe

section Corrector

variable {d : ℕ}
variable {μ : Measure (RegCoeffField d)}

theorem hasHorizontalGradient_zero
    (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ) :
    HasHorizontalGradient hstat 0 0 := by
  intro i
  simpa only [map_zero] using
    (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : Lp ℝ 2 μ)))

theorem HasHorizontalGradient.add
    {hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ}
    {φ ψ : Lp ℝ 2 μ} {F G : Lp (HilbertVec d) 2 μ}
    (hφ : HasHorizontalGradient hstat φ F)
    (hψ : HasHorizontalGradient hstat ψ G) :
    HasHorizontalGradient hstat (φ + ψ) (F + G) := by
  intro i
  convert (hφ i).add (hψ i) using 1
  · funext t
    exact map_add (koopman hstat (t • (Pi.single i 1 : Vec d))) φ ψ
  · exact (vectorL2Coord (μ := μ) i).map_add F G

theorem HasHorizontalGradient.smul
    {hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ}
    (c : ℝ) {φ : Lp ℝ 2 μ} {F : Lp (HilbertVec d) 2 μ}
    (hφ : HasHorizontalGradient hstat φ F) :
    HasHorizontalGradient hstat (c • φ) (c • F) := by
  intro i
  convert (hφ i).const_smul c using 1
  · funext t
    exact map_smul (koopman hstat (t • (Pi.single i 1 : Vec d))) c φ
  · exact (vectorL2Coord (μ := μ) i).map_smul c F

def horizontalGradientRange (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ) : Submodule ℝ
    (Lp (HilbertVec d) 2 μ) where
  carrier := {F | ∃ φ, HasHorizontalGradient hstat φ F}
  zero_mem' := ⟨0, hasHorizontalGradient_zero hstat⟩
  add_mem' := by
    rintro F G ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    exact ⟨φ + ψ, hφ.add hψ⟩
  smul_mem' := by
    rintro c F ⟨φ, hφ⟩
    exact ⟨c • φ, hφ.smul c⟩

def stationaryPotentialSubspace (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ) :
    Submodule ℝ (Lp (HilbertVec d) 2 μ) := (horizontalGradientRange hstat).topologicalClosure
end Corrector

/-- The canonical source-sign potential corrector for the zero-shell regular-field
law: minus the projection of the origin forcing onto the potential subspace. -/
noncomputable def zeroShellPotentialCorrector {d : ℕ}
    (P : ProbabilityMeasure (ShellSeq d))
    (hstat : ∀ z : Vec d,
      MeasurePreserving (translateReg (d := d) z) (zeroShellRegMeasure P) (zeroShellRegMeasure P))
    (e : Vec d)
    (hmem : MemLp (originForcing e) 2 (zeroShellRegMeasure P)) :
    Lp (HilbertVec d) 2 (zeroShellRegMeasure P) := by
  letI : CompleteSpace (stationaryPotentialSubspace (d := d) hstat) := by
    change CompleteSpace (horizontalGradientRange (d := d) hstat).topologicalClosure
    infer_instance
  exact -(stationaryPotentialSubspace hstat).starProjection
    (hmem.toLp (originForcing e))

section CorrectorCharacterization

variable {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
  (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) (zeroShellRegMeasure P)
    (zeroShellRegMeasure P))

instance potentialHasOrthogonalProjection :
    (stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat).HasOrthogonalProjection := by
  haveI : CompleteSpace (stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat) := by
    change CompleteSpace
      (horizontalGradientRange (μ := zeroShellRegMeasure P) hstat).topologicalClosure
    infer_instance
  infer_instance

theorem mem_potential_iff (F : Lp (HilbertVec d) 2 (zeroShellRegMeasure P)) :
    F ∈ stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat ↔
      F ∈ closure {G | ∃ φ, HasHorizontalGradient (μ := zeroShellRegMeasure P) hstat φ G} :=
  Iff.rfl

theorem inner_eq_zero_of_range
    {v : Lp (HilbertVec d) 2 (zeroShellRegMeasure P)}
    (h : ∀ (φ : Lp ℝ 2 (zeroShellRegMeasure P)) (F : Lp (HilbertVec d) 2 (zeroShellRegMeasure P)),
      HasHorizontalGradient (μ := zeroShellRegMeasure P) hstat φ F → inner ℝ v F = 0) :
    ∀ w ∈ stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat, inner ℝ v w = 0 := by
  intro w hw
  have hclosed : IsClosed {u : Lp (HilbertVec d) 2 (zeroShellRegMeasure P) | inner ℝ v u = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  refine hclosed.closure_subset_iff.mpr ?_ ((mem_potential_iff hstat w).mp hw)
  rintro u ⟨φ, hφ⟩
  exact h φ u hφ

/-- **The corrector characterization.**  The existential display of
`RealizesCstar` holds exactly when the canonical orthogonal-projection corrector
has the stated energy: membership plus criticality pin the witness. -/
theorem realizesCstar_iff_corrector (P : ProbabilityMeasure (ShellSeq d)) (c : ℝ) :
    RealizesCstar d P c ↔
      ∀ (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z)
          (zeroShellRegMeasure P) (zeroShellRegMeasure P)) (e : Vec d), vecNorm e = 1 →
        ∀ hmem : MemLp (originForcing e) 2 (zeroShellRegMeasure P),
          ‖zeroShellPotentialCorrector P hstat e hmem‖ ^ 2 = c * Real.log 3 := by
  have key : ∀ (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z)
      (zeroShellRegMeasure P) (zeroShellRegMeasure P)) (e : Vec d)
      (hmem : MemLp (originForcing e) 2 (zeroShellRegMeasure P))
      (chi : Lp (HilbertVec d) 2 (zeroShellRegMeasure P)),
      chi ∈ closure {F | ∃ φ, HasHorizontalGradient (μ := zeroShellRegMeasure P) hstat φ F} →
      (∀ (φ : Lp ℝ 2 (zeroShellRegMeasure P)) (F : Lp (HilbertVec d) 2 (zeroShellRegMeasure P)),
        HasHorizontalGradient (μ := zeroShellRegMeasure P) hstat φ F →
        inner ℝ (hmem.toLp (originForcing e) + chi) F = 0) →
      chi = zeroShellPotentialCorrector P hstat e hmem := by
    intro hstat e hmem chi hmemchi hcrit
    have hneg : -chi ∈ stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat :=
      neg_mem ((mem_potential_iff hstat chi).mpr hmemchi)
    have horth : ∀ w ∈ stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat,
        inner ℝ (hmem.toLp (originForcing e) - -chi) w = 0 := by
      have hz := inner_eq_zero_of_range hstat hcrit
      simpa only [sub_neg_eq_add] using hz
    have hproj := Submodule.eq_starProjection_of_mem_of_inner_eq_zero hneg horth
    have hcorr : zeroShellPotentialCorrector P hstat e hmem =
        -(stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat).starProjection
          (hmem.toLp (originForcing e)) := rfl
    rw [hcorr, hproj, neg_neg]
  constructor
  · intro h hstat e he hmem
    obtain ⟨chi, hmemchi, hcrit, hnorm⟩ := h hstat e he hmem
    rw [← key hstat e hmem chi hmemchi hcrit]
    exact hnorm
  · intro h hstat e he hmem
    refine ⟨zeroShellPotentialCorrector P hstat e hmem, ?_, ?_, h hstat e he hmem⟩
    · refine (mem_potential_iff hstat _).mp ?_
      exact neg_mem (Submodule.starProjection_apply_mem _ _)
    · intro φ F hF
      have hmemF : F ∈ stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat :=
        (mem_potential_iff hstat F).mpr (subset_closure ⟨φ, hF⟩)
      have hcorr : zeroShellPotentialCorrector P hstat e hmem =
          -(stationaryPotentialSubspace (μ := zeroShellRegMeasure P) hstat).starProjection
            (hmem.toLp (originForcing e)) := rfl
      rw [hcorr, ← sub_eq_add_neg]
      exact Submodule.starProjection_inner_eq_zero _ _ hmemF

end CorrectorCharacterization

end

end GeneratorRenormalization
end StatementAudit
end Algsuperdiff
