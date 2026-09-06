import Mathlib
import Algsuperdiff.MainTheorems

/-!
# The stream process read on live paths

The repository builds the diffusion of the stream field on the one-point
compactification of `ℝ^d`, in the metric of an exhaustion function
(`Algsuperdiff.Section5.Field.streamProcess`).  The `Superdiffusivity`
challenge states its theorem for laws on *live* continuous paths, in the metric
of `ℝ^d` itself.  This file carries the compactified law back to live path
space.

Post-composition with the coercion `ℝ^d → OnePoint ℝ^d` is a continuous
injection of Polish path spaces, hence a measurable embedding
(`measurableEmbedding_pathPostcomp`), and its range is exactly the set of
compactified paths that never reach the added point
(`mem_range_pathPostcomp`).  The compactified law of a live starting point is
carried by that range (`streamProcess_ae_stays_live`), so its comap along the
embedding — `liveLaw` — is a probability law on live paths whose pushforward is
the compactified law again (`map_pathPostcomp_liveLaw`).  Integrals and lower
integrals transfer (`integral_liveLaw`, `lintegral_liveLaw`), and the live law
starts where it is told (`liveLaw_start`).
-/

namespace SuperdiffusionAudit.Support.SDLiveLaw

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open DivergenceFormProcess.Form DivergenceFormProcess.LiveRestriction
open Homogenization MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The path embedding -/

section Embedding

variable {X Y : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [T2Space Y]

omit [CompleteSpace X] [SecondCountableTopology X] [T2Space Y] in
/-- Post-composition with an injective continuous map is injective on paths. -/
theorem injective_pathPostcomp {f : C(X, Y)} (hf : Function.Injective f) :
    Function.Injective (pathPostcomp f) := by
  intro p q h
  refine ContinuousPath.ext fun t => ?_
  have hval := congrArg (fun r : ContinuousPath Y => r t) h
  simp only [pathPostcomp_apply] at hval
  exact hf hval

/-- **Post-composition with an injective continuous map is a measurable
embedding of path spaces.**  The source is a Polish space and the target is a
Hausdorff Borel space, so Lusin--Souslin applies. -/
theorem measurableEmbedding_pathPostcomp {f : C(X, Y)} (hf : Function.Injective f) :
    MeasurableEmbedding (pathPostcomp f) :=
  (continuous_pathPostcomp f).measurableEmbedding (injective_pathPostcomp hf)

end Embedding

variable {d : ℕ}

/-- A compactified path that never reaches the added point is the image of a
live path: the coercion is an open embedding, so the pointwise retraction of
such a path is continuous. -/
theorem mem_range_pathPostcomp {X : Type*} [TopologicalSpace X] [Nonempty X]
    (path : ContinuousPath (OnePoint X))
    (h : ∀ t : NNReal, path t ∈ Set.range ((↑) : X → OnePoint X)) :
    path ∈ Set.range (pathPostcomp (liveEmbedding X)) := by
  classical
  set x0 : X := Classical.arbitrary X
  have hcoe : ∀ t : NNReal, ((onePointRetract x0 (path t) : X) : OnePoint X) = path t := by
    intro t
    obtain ⟨y, hy⟩ := h t
    rw [← hy]
    rfl
  have hcont : Continuous fun t : NNReal => onePointRetract x0 (path t) := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff]
    exact path.continuous.congr fun t => (hcoe t).symm
  exact ⟨⟨_, hcont⟩, ContinuousPath.ext fun t => hcoe t⟩

variable [NeZero d] (M : ABKModel d) (omega : FullSample d M.gamma)

/-- The one-point regularity witness of the stream field. -/
abbrev streamReg : (streamWholeSpaceResolvent M omega).OnePointRegular :=
  (streamExhaustionTailInput M omega).toOnePointRegular

/-- The stream process is the continuous-path process of the compactified
kernel semigroup. -/
theorem streamProcess_eq :
    letI := (streamReg M omega).metricSpace
    letI := (streamReg M omega).completeSpace
    streamProcess M omega =
      IsConservative.continuousProcess
        (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
        (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup := rfl

theorem isMarkovKernel_streamProcess :
    letI := (streamReg M omega).metricSpace
    letI := (streamReg M omega).completeSpace
    IsMarkovKernel (streamProcess M omega) :=
  (onePointProcess_spec (streamReg M omega)).1

/-! ## 2. The live law -/

/-- **The stream law on live paths**: the comap of the compactified law along
the path embedding. -/
def liveLaw (x : Vec d) : Measure (ContinuousPath (Vec d)) :=
  letI := (streamReg M omega).metricSpace
  letI := (streamReg M omega).completeSpace
  Measure.comap (pathPostcomp (liveEmbedding (Vec d)))
    (streamProcess M omega (x : OnePoint (Vec d)))

/-- The compactified law of a live starting point is carried by the range of
the path embedding, and the live law pushes forward to it. -/
theorem map_pathPostcomp_liveLaw :
    letI := (streamReg M omega).metricSpace
    letI := (streamReg M omega).completeSpace
    ∀ x : Vec d,
      Measure.map (pathPostcomp (liveEmbedding (Vec d))) (liveLaw M omega x) =
        streamProcess M omega (x : OnePoint (Vec d)) := by
  letI := (streamReg M omega).metricSpace
  letI := (streamReg M omega).completeSpace
  intro x
  have hae : ∀ᵐ path ∂streamProcess M omega (x : OnePoint (Vec d)),
      path ∈ Set.range (pathPostcomp (liveEmbedding (Vec d))) := by
    filter_upwards [streamProcess_ae_stays_live M omega x] with path hpath
    exact mem_range_pathPostcomp path
      ((ContinuousPath.exitTime_eq_top_iff _ path).mp hpath)
  rw [liveLaw, (measurableEmbedding_pathPostcomp injective_liveCoe).map_comap]
  exact Measure.restrict_eq_self_of_ae_mem hae

instance isProbabilityMeasure_liveLaw (x : Vec d) :
    IsProbabilityMeasure (liveLaw M omega x) := by
  letI := (streamReg M omega).metricSpace
  letI := (streamReg M omega).completeSpace
  haveI := isMarkovKernel_streamProcess M omega
  refine ⟨?_⟩
  have h : Measure.map (pathPostcomp (liveEmbedding (Vec d))) (liveLaw M omega x) Set.univ =
      streamProcess M omega (x : OnePoint (Vec d)) Set.univ := by
    rw [map_pathPostcomp_liveLaw M omega x]
  rw [Measure.map_apply
      (measurableEmbedding_pathPostcomp (Y := OnePoint (Vec d)) injective_liveCoe).measurable
      MeasurableSet.univ, Set.preimage_univ] at h
  rw [h, measure_univ]

/-- Integrals and lower integrals transfer between the two laws. -/
theorem integral_liveLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    letI := (streamReg M omega).metricSpace
    letI := (streamReg M omega).completeSpace
    ∀ (x : Vec d) (G : ContinuousPath (OnePoint (Vec d)) → E),
      AEStronglyMeasurable G (streamProcess M omega (x : OnePoint (Vec d))) →
      (∫ path, G (pathPostcomp (liveEmbedding (Vec d)) path) ∂liveLaw M omega x) =
        ∫ path, G path ∂streamProcess M omega (x : OnePoint (Vec d)) := by
  letI := (streamReg M omega).metricSpace
  letI := (streamReg M omega).completeSpace
  intro x G hG
  rw [← map_pathPostcomp_liveLaw M omega x] at hG ⊢
  rw [integral_map
    (measurableEmbedding_pathPostcomp (Y := OnePoint (Vec d)) injective_liveCoe
      ).measurable.aemeasurable hG]

theorem lintegral_liveLaw :
    letI := (streamReg M omega).metricSpace
    letI := (streamReg M omega).completeSpace
    ∀ (x : Vec d) (G : ContinuousPath (OnePoint (Vec d)) → ℝ≥0∞), Measurable G →
      (∫⁻ path, G (pathPostcomp (liveEmbedding (Vec d)) path) ∂liveLaw M omega x) =
        ∫⁻ path, G path ∂streamProcess M omega (x : OnePoint (Vec d)) := by
  letI := (streamReg M omega).metricSpace
  letI := (streamReg M omega).completeSpace
  intro x G hG
  rw [← map_pathPostcomp_liveLaw M omega x, lintegral_map hG
    (measurableEmbedding_pathPostcomp (Y := OnePoint (Vec d)) injective_liveCoe).measurable]

/-- **Work item F.**  The live law starts where it is told. -/
theorem liveLaw_start (x : Vec d) :
    liveLaw M omega x {path : ContinuousPath (Vec d) | path 0 = x} = 1 := by
  letI := (streamReg M omega).metricSpace
  letI := (streamReg M omega).completeSpace
  have hev : Measurable (fun path : ContinuousPath (OnePoint (Vec d)) => path 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := OnePoint (Vec d)) 0
  have hdirac : Measure.map (fun path : ContinuousPath (OnePoint (Vec d)) => path 0)
      (streamProcess M omega (x : OnePoint (Vec d))) = Measure.dirac (x : OnePoint (Vec d)) := by
    rw [streamProcess_eq M omega]
    have hzero := IsConservative.continuousProcess_map_eval_zero
      (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
      (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
      (streamReg M omega).kolmogorovRegular
    have hker : ((IsConservative.continuousProcess
        (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
        (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup).map
          fun path : ContinuousPath (OnePoint (Vec d)) => path 0) (x : OnePoint (Vec d)) =
        Kernel.id (x : OnePoint (Vec d)) := by rw [hzero]
    rwa [Kernel.map_apply _ hev, Kernel.id_apply] at hker
  have hmeasS : MeasurableSet ((fun path : ContinuousPath (OnePoint (Vec d)) => path 0) ⁻¹'
      {(x : OnePoint (Vec d))}) := hev (measurableSet_singleton _)
  have hpre : {path : ContinuousPath (Vec d) | path 0 = x} =
      pathPostcomp (liveEmbedding (Vec d)) ⁻¹'
        ((fun path : ContinuousPath (OnePoint (Vec d)) => path 0) ⁻¹'
          {(x : OnePoint (Vec d))}) := by
    ext path
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      pathPostcomp_apply, liveEmbedding_apply]
    exact ⟨fun h => by rw [h], fun h => injective_liveCoe h⟩
  rw [hpre, ← Measure.map_apply
      (measurableEmbedding_pathPostcomp (Y := OnePoint (Vec d)) injective_liveCoe).measurable
      hmeasS, map_pathPostcomp_liveLaw M omega x,
    ← Measure.map_apply hev (measurableSet_singleton _), hdirac]
  simp

end

end SuperdiffusionAudit.Support.SDLiveLaw
