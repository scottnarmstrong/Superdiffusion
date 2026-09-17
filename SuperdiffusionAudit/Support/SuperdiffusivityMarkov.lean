import SuperdiffusionAudit.Superdiffusivity.SolutionBasic
import SuperdiffusionAudit.Support.SuperdiffusivityLiveLaw

namespace SuperdiffusionAudit.Support.SDMarkov

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open DivergenceFormProcess.Form DivergenceFormProcess.LiveRestriction
open Homogenization MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

private theorem pathHistory_eq_comap_pathPostcomp (s : ℝ≥0) :
    Algsuperdiff.StatementAudit.Superdiffusivity.pathHistory (d := d) s =
      MeasurableSpace.comap (pathPostcomp (liveEmbedding (Vec d)))
        (ContinuousPath.canonicalFiltration (alpha := OnePoint (Vec d)) s) := by
  rw [Algsuperdiff.StatementAudit.Superdiffusivity.pathHistory,
    ContinuousPath.canonicalFiltration,
    MeasurableSpace.comap_iSup]
  apply le_antisymm
  · refine iSup_le fun t => ?_
    refine le_iSup_of_le t ?_
    rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap (fun path : ContinuousPath (Vec d) => path t)
        inferInstance ≤
      MeasurableSpace.comap (fun path : ContinuousPath (Vec d) =>
        ((path t : Vec d) : OnePoint (Vec d))) inferInstance
    have hf : (fun path : ContinuousPath (Vec d) =>
        ((path t : Vec d) : OnePoint (Vec d))) =
        ((fun x : Vec d => (x : OnePoint (Vec d))) ∘ fun path => path t) := rfl
    rw [hf, ← MeasurableSpace.comap_comp,
      OnePoint.isOpenEmbedding_coe.measurableEmbedding.comap_eq]
  · refine iSup_le fun t => ?_
    refine le_iSup_of_le t ?_
    rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap (fun path : ContinuousPath (Vec d) =>
        ((path t : Vec d) : OnePoint (Vec d))) inferInstance ≤
      MeasurableSpace.comap (fun path : ContinuousPath (Vec d) => path t) inferInstance
    have hf : (fun path : ContinuousPath (Vec d) =>
        ((path t : Vec d) : OnePoint (Vec d))) =
        ((fun x : Vec d => (x : OnePoint (Vec d))) ∘ fun path => path t) := rfl
    rw [hf, ← MeasurableSpace.comap_comp,
      OnePoint.isOpenEmbedding_coe.measurableEmbedding.comap_eq]

private theorem pathPostcomp_shift (s : ℝ≥0) (path : ContinuousPath (Vec d)) :
    pathPostcomp (liveEmbedding (Vec d))
        (Algsuperdiff.StatementAudit.Superdiffusivity.pathShift s path) =
      ContinuousPath.shift s (pathPostcomp (liveEmbedding (Vec d)) path) := by
  ext t
  rfl

theorem hasMarkovRestart_liveLaw [NeZero d] (M : ABKModel d)
    (omega : Algsuperdiff.Section5.Field.FullSample d M.gamma) :
    Algsuperdiff.StatementAudit.Superdiffusivity.HasMarkovRestart
      (SDLiveLaw.liveLaw M omega) := by
  let := (SDLiveLaw.streamReg M omega).metricSpace
  let := (SDLiveLaw.streamReg M omega).completeSpace
  let e := pathPostcomp (liveEmbedding (Vec d))
  have he : MeasurableEmbedding e :=
    SDLiveLaw.measurableEmbedding_pathPostcomp injective_liveCoe
  have hQ : Measurable (SDLiveLaw.liveLaw M omega) := by
    rw [Measure.measurable_measure]
    intro C hC
    have heC : MeasurableSet (e '' C) := he.measurableSet_image.mpr hC
    have hpre : e ⁻¹' (e '' C) = C := Set.preimage_image_eq C he.injective
    have hval : ∀ x : Vec d,
        SDLiveLaw.liveLaw M omega x C =
          streamProcess M omega (x : OnePoint (Vec d)) (e '' C) := by
      intro x
      rw [← hpre, ← Measure.map_apply he.measurable heC,
        SDLiveLaw.map_pathPostcomp_liveLaw]
      have him : e '' (e ⁻¹' (e '' C)) = e '' C := by
        rw [hpre]
      rw [him]
    simp_rw [hval]
    exact (streamProcess M omega).measurable_coe heC |>.comp
      OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurable
  refine ⟨hQ, ?_⟩
  intro x s A hA B hB
  rw [pathHistory_eq_comap_pathPostcomp] at hA
  change ∃ D, MeasurableSet[ContinuousPath.canonicalFiltration
      (alpha := OnePoint (Vec d)) s] D ∧ e ⁻¹' D = A at hA
  obtain ⟨D, hD, rfl⟩ := hA
  have hD' : MeasurableSet D :=
    (ContinuousPath.canonicalFiltration (alpha := OnePoint (Vec d))).le s D hD
  let E := e '' B
  have hE : MeasurableSet E := he.measurableSet_image.mpr hB
  have hpreE : e ⁻¹' E = B := Set.preimage_image_eq B he.injective
  let P := (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
  let hP := (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
  let Q := IsConservative.continuousProcess P hP
  have hre :=
    (streamWholeSpaceResolvent M omega).isFellerKernelSemigroup_onePointKernelSemigroup
      |>.continuousProcess_restrict_map_shift P hP
        (SDLiveLaw.streamReg M omega).kolmogorovRegular
        (x : OnePoint (Vec d)) s D hD
  have hscalar := congrArg (fun mu : Measure (ContinuousPath (OnePoint (Vec d))) => mu E) hre
  change ((((Q (x : OnePoint (Vec d))).restrict D).map
      (ContinuousPath.shift s)) E =
    ((Kernel.comap Q (ContinuousPath.coordinateProcess s)
      (ContinuousPath.measurable_coordinateProcess s)) ∘ₘ
        ((Q (x : OnePoint (Vec d))).restrict D)) E) at hscalar
  have hl : ((((Q (x : OnePoint (Vec d))).restrict D).map
      (ContinuousPath.shift s)) E) =
      Q (x : OnePoint (Vec d)) (ContinuousPath.shift s ⁻¹' E ∩ D) := by
    erw [Measure.map_apply (ContinuousPath.measurable_shift_fixed s) hE,
      Measure.restrict_apply (ContinuousPath.measurable_shift_fixed s hE)]
    rfl
  have hr :
      ((Kernel.comap Q (ContinuousPath.coordinateProcess s)
        (ContinuousPath.measurable_coordinateProcess s)) ∘ₘ
          ((Q (x : OnePoint (Vec d))).restrict D)) E =
        ∫⁻ z in D, Q (z s) E ∂Q (x : OnePoint (Vec d)) := by
    erw [Measure.bind_apply hE (Kernel.aemeasurable _)]
    change (∫⁻ z, Q (z s) E ∂(Q (x : OnePoint (Vec d))).restrict D) = _
    rfl
  have hscalar' := hl.symm.trans (hscalar.trans hr)
  dsimp only [Q] at hscalar'
  erw [← SDLiveLaw.streamProcess_eq M omega] at hscalar'
  erw [← SDLiveLaw.map_pathPostcomp_liveLaw M omega x] at hscalar'
  erw [Measure.map_apply he.measurable
      ((ContinuousPath.measurable_shift_fixed s hE).inter hD')] at hscalar'
  have hset : e ⁻¹' (ContinuousPath.shift s ⁻¹' E ∩ D) =
      e ⁻¹' D ∩ Algsuperdiff.StatementAudit.Superdiffusivity.pathShift s ⁻¹' B := by
    ext path
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    have hs := pathPostcomp_shift (d := d) s path
    rw [← hs, ← hpreE]
    tauto
  rw [hset] at hscalar'
  erw [SDLiveLaw.map_pathPostcomp_liveLaw M omega x] at hscalar'
  have hint :
      (∫⁻ z in D, streamProcess M omega (z s) E
          ∂streamProcess M omega (x : OnePoint (Vec d))) =
        ∫⁻ path in e ⁻¹' D, SDLiveLaw.liveLaw M omega (path s) B
          ∂SDLiveLaw.liveLaw M omega x := by
    have hfun : Measurable (fun z : ContinuousPath (OnePoint (Vec d)) =>
        streamProcess M omega (z s) E) :=
      (streamProcess M omega).measurable_coe hE |>.comp
        (ContinuousPath.measurable_coordinateProcess s)
    have hG : Measurable (D.indicator (fun z : ContinuousPath (OnePoint (Vec d)) =>
        streamProcess M omega (z s) E)) := hfun.indicator hD'
    rw [← SDLiveLaw.map_pathPostcomp_liveLaw M omega x]
    rw [← MeasureTheory.lintegral_indicator hD']
    rw [MeasureTheory.lintegral_map hG he.measurable]
    rw [← MeasureTheory.lintegral_indicator (he.measurable hD')]
    apply lintegral_congr
    intro path
    by_cases hp : path ∈ e ⁻¹' D
    · have hep : e path ∈ D := hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hep]
      rw [← hpreE, ← Measure.map_apply he.measurable hE,
        SDLiveLaw.map_pathPostcomp_liveLaw]
      rfl
    · have hep : e path ∉ D := hp
      simp [Set.indicator, hp, hep]
  exact hscalar'.trans hint

end
end SuperdiffusionAudit.Support.SDMarkov
