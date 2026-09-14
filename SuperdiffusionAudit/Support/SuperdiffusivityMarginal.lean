import Mathlib
import Algsuperdiff.MainTheorems
import SuperdiffusionAudit.Support.LaplaceUniqueness
import SuperdiffusionAudit.Support.SuperdiffusivityLiveLaw
import SuperdiffusionAudit.Support.SuperdiffusivityResolvent

/-!
# The resolvent of the live stream law

The challenge characterizes a diffusion of a coefficient field by the Laplace
transform in time of its one-point marginals.  This file computes that
transform for the live stream law of `SuperdiffusivityLiveLaw.lean` and
identifies it with the analytic minimal resolvent.

The route is the killed resolvent of the compactified process at the exit from
the live space, which the process library identifies with the kernel resolvent
of the live semigroup
(`PositiveC0ContractiveResolvent.OnePointRegular.killedResolvent_live_eq_kernelResolvent`);
the killing does nothing because the process a.s. never leaves the live space.
The stream field's kernel resolvent is the analytic minimal resolvent
(`kernelResolventIdentifiesAnalyticMinimal_stream`), and that is the supremum
of the cube resolvents, so the live law is a diffusion of the stream field in
the challenge's sense (`isDiffusionOf_liveLaw`).

Conversely, the characterization pins the one-point marginals: the time
integrand is bounded and continuous, so the equality of Laplace transforms
upgrades to equality at every positive time
(`SuperdiffusionAudit.Support.LaplaceUniqueness`), and equality of integrals
against the nonnegative continuous compactly supported functions is equality
of the marginals (`map_eval_eq_liveLaw`).
-/

namespace SuperdiffusionAudit.Support.SDMarginal

open Algsuperdiff.StatementAudit.Superdiffusivity
open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open DivergenceFormProcess.Form DivergenceFormProcess.LiveRestriction
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.PositiveC0ContractiveResolvent
open MeasureTheory ProbabilityTheory
open SuperdiffusionAudit.Support.SDLiveLaw SuperdiffusionAudit.Support.SDResolvent
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Test functions -/

/-- A continuous compactly supported function is bounded. -/
theorem exists_bound_of_hasCompactSupport {f : Vec d → ℝ} (hcont : Continuous f)
    (hsupp : HasCompactSupport f) : ∃ C : ℝ, 0 < C ∧ ∀ y, |f y| ≤ C := by
  obtain ⟨C, hC⟩ := hsupp.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨|C| + 1, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · have := hC y hy
    rw [Real.norm_eq_abs] at this
    have hCC : C ≤ |C| := le_abs_self C
    linarith
  · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero]
    positivity

/-- A test function of the challenge is bounded. -/
theorem exists_bound_isResolventTest {f : Vec d → ℝ} (hf : IsResolventTest f) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, |f y| ≤ C :=
  exists_bound_of_hasCompactSupport hf.1 hf.2.1

/-- A bounded continuous function is integrable against a finite measure. -/
theorem integrable_of_bounded {mu : Measure (Vec d)} [IsFiniteMeasure mu]
    {psi : Vec d → ℝ} (hc : Continuous psi) {C : ℝ} (hC : ∀ y, |psi y| ≤ C) :
    Integrable psi mu :=
  Integrable.mono' (integrable_const C) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)

/-- The one-point integrals of a bounded continuous function against a law on
continuous paths are continuous in time. -/
theorem continuous_pathIntegral (nu : Measure (ContinuousPath (Vec d)))
    [IsFiniteMeasure nu] {f : Vec d → ℝ} (hcont : Continuous f) {C : ℝ}
    (hbound : ∀ y, |f y| ≤ C) :
    Continuous fun s : ℝ => ∫ path, f (path s.toNNReal) ∂nu := by
  refine continuous_of_dominated (bound := fun _ => C) (fun s => ?_) (fun s => ?_)
    (integrable_const C) ?_
  · exact ((hcont.comp (ContinuousPath.continuous_eval (alpha := Vec d)
      s.toNNReal)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun path => by
      simpa [Real.norm_eq_abs] using hbound (path s.toNNReal)
  · refine Filter.Eventually.of_forall fun path => ?_
    exact hcont.comp (path.continuous.comp continuous_real_toNNReal)

/-- A one-point integral of a bounded function is bounded. -/
theorem abs_pathIntegral_le (nu : Measure (ContinuousPath (Vec d))) [IsProbabilityMeasure nu]
    {f : Vec d → ℝ} {C : ℝ} (hC : ∀ y, |f y| ≤ C) (s : ℝ) :
    |∫ path, f (path s.toNNReal) ∂nu| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := nu) (C := C)
    (f := fun path : ContinuousPath (Vec d) => f (path s.toNNReal))
    (Filter.Eventually.of_forall fun path => by
      simpa [Real.norm_eq_abs] using hC (path s.toNNReal))
  simpa [Real.norm_eq_abs, measureReal_def] using h


variable [NeZero d] (M : ABKModel d)
  (omega : Algsuperdiff.Section5.Field.FullSample d M.gamma)

theorem streamWholeSpaceResolvent_eq :
    streamWholeSpaceResolvent M omega =
      streamAnalyticMinimalPositiveC0ContractiveResolvent M omega := rfl

/-! ## 2. The Laplace transform of the live law -/

section Laplace

variable {lam : ℝ} (hlam : 0 < lam) {f : Vec d → ℝ} (hcont : Continuous f)
  (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, |f y| ≤ 1) (x : Vec d)

include hcont hf1 in
/-- The time integrand of the live law, at a normalized datum. -/
private theorem integrable_pathIntegral (t : ℝ) :
    Integrable (fun path : ContinuousPath (Vec d) => f (path t.toNNReal))
      (liveLaw M omega x) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((hcont.comp (ContinuousPath.continuous_eval (alpha := Vec d)
      t.toNNReal)).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun path => by
    simpa [Real.norm_eq_abs] using hf1 (path t.toNNReal)

include hcont hf0 hf1 in
/-- The lower integral of the zero extension against the compactified law is
the ordinary integral against the live law. -/
private theorem lintegral_onePointLiveExtension (t : ℝ) :
    letI := (streamReg M omega).metricSpace
    letI := (streamReg M omega).completeSpace
    (∫⁻ path, onePointLiveExtension (ENNReal.ofReal ∘ f) (path t.toNNReal)
        ∂streamProcess M omega (x : OnePoint (Vec d))) =
      ENNReal.ofReal (∫ path, f (path t.toNNReal) ∂liveLaw M omega x) := by
  let := (streamReg M omega).metricSpace
  let := (streamReg M omega).completeSpace
  have hFenn : Measurable (onePointLiveExtension (ENNReal.ofReal ∘ f)) :=
    measurable_onePointLiveExtension (ENNReal.measurable_ofReal.comp hcont.measurable)
  have hmeas : Measurable fun path : ContinuousPath (OnePoint (Vec d)) =>
      onePointLiveExtension (ENNReal.ofReal ∘ f) (path t.toNNReal) :=
    hFenn.comp (ContinuousPath.measurable_coordinateProcess
      (alpha := OnePoint (Vec d)) t.toNNReal)
  rw [← lintegral_liveLaw M omega x _ hmeas]
  have hpt : ∀ path : ContinuousPath (Vec d),
      onePointLiveExtension (ENNReal.ofReal ∘ f)
          ((pathPostcomp (liveEmbedding (Vec d)) path) t.toNNReal) =
        ENNReal.ofReal (f (path t.toNNReal)) := by
    intro path
    simp [pathPostcomp_apply]
  simp only [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pathIntegral M omega hcont hf1 x t)
    (Filter.Eventually.of_forall fun path => hf0 _)]

include hcont hf0 hf1 hlam in
/-- **The Laplace transform of the live law is the analytic minimal
resolvent**, at a datum normalized by one. -/
theorem integral_exp_neg_mul_liveLaw :
    (∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) *
        ∫ path, f (path s.toNNReal) ∂liveLaw M omega x) =
      ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent ⟨lam, hlam⟩ f
        hcont.measurable hf1 x).toReal := by
  let := (streamReg M omega).metricSpace
  let := (streamReg M omega).completeSpace
  set g : ℝ → ℝ := fun s => ∫ path, f (path s.toNNReal) ∂liveLaw M omega x with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s =>
    integral_nonneg fun path => hf0 _
  have hg1 : ∀ s, |g s| ≤ 1 := by
    intro s
    rw [abs_of_nonneg (hg0 s)]
    calc g s ≤ ∫ _path, (1 : ℝ) ∂liveLaw M omega x := by
          refine integral_mono (integrable_pathIntegral M omega hcont hf1 x s)
            (integrable_const 1) fun path => ?_
          exact (le_abs_self _).trans (hf1 _)
      _ = 1 := by simp
  have hgcont : Continuous g :=
    continuous_pathIntegral (liveLaw M omega x) hcont hf1
  -- the killed resolvent expands to the Laplace transform of `g`
  have hFenn : Measurable (onePointLiveExtension (ENNReal.ofReal ∘ f)) :=
    measurable_onePointLiveExtension (ENNReal.measurable_ofReal.comp hcont.measurable)
  have hexpand : IsConservative.killedResolvent
      (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
      (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
      (Set.range ((↑) : Vec d → OnePoint (Vec d))) OnePoint.isOpen_range_coe lam
      (onePointLiveExtension (ENNReal.ofReal ∘ f)) (x : OnePoint (Vec d)) =
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t) * g t) := by
    unfold IsConservative.killedResolvent
    refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hkk := IsConservative.lintegral_killedKernel
      (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
      (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
      (Set.range ((↑) : Vec d → OnePoint (Vec d))) OnePoint.isOpen_range_coe
      (Real.toNNReal t) (x : OnePoint (Vec d)) hFenn
    refine Eq.trans (congrArg (fun z => ENNReal.ofReal (Real.exp (-lam * t)) * z) hkk) ?_
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [← streamProcess_eq M omega,
      ← lintegral_onePointLiveExtension M omega hcont hf0 hf1 x t]
    refine lintegral_congr_ae ?_
    filter_upwards [streamProcess_ae_stays_live M omega x] with path hpath
    refine Set.indicator_of_mem ?_ _
    show ((t.toNNReal : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime _ path
    exact lt_of_lt_of_eq ENNReal.coe_lt_top hpath.symm
  have hlive := (streamReg M omega).killedResolvent_live_eq_kernelResolvent lam
    (ENNReal.measurable_ofReal.comp hcont.measurable) x
  have hker := kernelResolventIdentifiesAnalyticMinimal_stream M omega ⟨lam, hlam⟩
    hcont.measurable hf0 hf1 x
  have hker' : (streamAnalyticMinimalPositiveC0ContractiveResolvent M omega
      ).kernelSemigroup.kernelResolvent lam (ENNReal.ofReal ∘ f) x =
      (streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent ⟨lam, hlam⟩ f
        hcont.measurable hf1 x := by
    simpa [Function.comp_def] using hker
  rw [hexpand, streamWholeSpaceResolvent_eq M omega] at hlive
  rw [← hlive] at hker'
  -- convert the lower integral of the Laplace transform to a Bochner integral
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * g s) (Set.Ioi 0) := by
    have h1 := (exp_neg_integrableOn_Ioi (0 : ℝ) hlam).bdd_mul (f := g) (c := 1)
      hgcont.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hg1 s)
    simpa [IntegrableOn, mul_comm] using h1
  have hofReal : ENNReal.ofReal (∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) * g s) =
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s) * g s) :=
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun s => mul_nonneg (Real.exp_nonneg _) (hg0 s))
  rw [← hofReal] at hker'
  rw [← hker', ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioi fun s _ =>
    mul_nonneg (Real.exp_nonneg _) (hg0 s)

end Laplace

/-! ## 3. The live law is a diffusion of the stream field -/

/-- The supremum of any cube-resolvent family is the Laplace transform of the
live law: the family is the analytic one, and the general datum is reduced to a
normalized one by homogeneity. -/
theorem iSup_eq_integral_exp_neg_mul_liveLaw {lam : ℝ} (hlam : 0 < lam)
    {f : Vec d → ℝ} (hf : IsResolventTest f) {v : ℕ → Vec d → ℝ}
    (hv : ∀ m, IsCubeResolvent (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
      lam f m (v m)) (x : Vec d) :
    (⨆ m, v m x) =
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) *
        ∫ path, f (path s.toNNReal) ∂liveLaw M omega x := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_isResolventTest hf
  obtain ⟨hcont, -, hf0⟩ := hf
  set A := streamWholeSpaceAnalyticData M omega with hA
  set g : Vec d → ℝ := fun y => C⁻¹ * f y with hgdef
  have hgcont : Continuous g := continuous_const.mul hcont
  have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (by positivity) (hf0 y)
  have hg1 : ∀ y, |g y| ≤ 1 := by
    intro y
    rw [hgdef, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ C⁻¹)]
    rw [inv_mul_le_iff₀ hC0, mul_one]
    exact hC y
  have hfg : ∀ y, C * g y = f y := by
    intro y
    rw [hgdef]
    field_simp
  have hcf : ∀ y, |C * g y| ≤ |C| * 1 := by
    intro y
    rw [hfg y, abs_of_pos hC0]
    linarith [hC y]
  -- the family is the analytic one
  have hvalue : ∀ m, v m x =
      C * A.analyticCubeResolvent ⟨lam, hlam⟩ g hgcont.measurable hg1 m x := by
    intro m
    have h1 : v m = A.analyticCubeResolvent ⟨lam, hlam⟩ f hcont.measurable hC m :=
      eq_analyticCubeResolvent_of_isCubeResolvent A hlam hcont.measurable hC m (hv m)
    have h2 : A.analyticCubeResolvent ⟨lam, hlam⟩ f hcont.measurable hC m x =
        A.analyticCubeResolvent ⟨lam, hlam⟩ (fun y => C * g y)
          (hgcont.measurable.const_mul C) hcf m x :=
      A.analyticCubeResolvent_eq_of_eqOn ⟨lam, hlam⟩ hcont.measurable
        (hgcont.measurable.const_mul C) hC hcf m (fun y _ => (hfg y).symm) x
    rw [h1, h2, A.analyticCubeResolvent_smul ⟨lam, hlam⟩ C hgcont.measurable hg1 hcf m x]
  -- the supremum, and the Laplace transform at the normalized datum
  have hsup : (⨆ m, v m x) =
      C * ⨆ m, A.analyticCubeResolvent ⟨lam, hlam⟩ g hgcont.measurable hg1 m x := by
    rw [Real.mul_iSup_of_nonneg hC0.le]
    exact iSup_congr hvalue
  have hnorm := integral_exp_neg_mul_liveLaw M omega hlam hgcont hg0 hg1 x
  rw [hsup, iSup_analyticCubeResolvent A ⟨lam, hlam⟩ hgcont.measurable hg0 zero_le_one hg1 x,
    ← hnorm]
  -- scale back
  have hscale : ∀ s : ℝ, (∫ path, g (path s.toNNReal) ∂liveLaw M omega x) =
      C⁻¹ * ∫ path, f (path s.toNNReal) ∂liveLaw M omega x := by
    intro s
    rw [hgdef]
    exact integral_const_mul _ _
  simp only [hscale]
  rw [show (fun s : ℝ => Real.exp (-lam * s) *
      (C⁻¹ * ∫ path, f (path s.toNNReal) ∂liveLaw M omega x)) =
      fun s : ℝ => C⁻¹ * (Real.exp (-lam * s) *
        ∫ path, f (path s.toNNReal) ∂liveLaw M omega x) from funext fun s => by ring,
    integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hC0.ne', one_mul]

/-- **Work item E.**  The live stream law is a diffusion of the stream field in
the challenge's sense. -/
theorem isDiffusionOf_liveLaw :
    IsDiffusionOf (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
      (liveLaw M omega) := by
  refine ⟨fun x => inferInstance, fun x => liveLaw_start M omega x, ?_⟩
  intro lam hlam f hf v hv x
  exact (iSup_eq_integral_exp_neg_mul_liveLaw M omega hlam hf hv x).symm

/-! ## 4. The one-point marginals are pinned -/

/-- The Laplace transforms of the two path integrals agree at every positive
shift. -/
private theorem integral_exp_neg_mul_eq_of_isDiffusionOf
    (Q : Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : IsDiffusionOf (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega) Q)
    {f : Vec d → ℝ}
    (hf : IsResolventTest f) (x : Vec d) {lam : ℝ} (hlam : 0 < lam) :
    (∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) * ∫ path, f (path s.toNNReal) ∂Q x) =
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) *
        ∫ path, f (path s.toNNReal) ∂liveLaw M omega x := by
  obtain ⟨C, -, hC⟩ := exists_bound_isResolventTest hf
  set A := streamWholeSpaceAnalyticData M omega with hA
  have hv : ∀ m, IsCubeResolvent (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
      lam f m
      (A.analyticCubeResolvent ⟨lam, hlam⟩ f hf.1.measurable hC m) := fun m =>
    isCubeResolvent_analyticCubeResolvent A hlam hf.1.measurable hC m
  rw [hQ.2.2 lam hlam f hf _ hv x,
    iSup_eq_integral_exp_neg_mul_liveLaw M omega hlam hf hv x]

/-- The one-point integrals of a test function agree at every positive time. -/
theorem integral_eval_eq_of_isDiffusionOf (Q : Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : IsDiffusionOf (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega) Q)
    {f : Vec d → ℝ}
    (hf : IsResolventTest f) (x : Vec d) {t : ℝ} (ht : 0 < t) :
    (∫ path, f (path t.toNNReal) ∂Q x) = ∫ path, f (path t.toNNReal) ∂liveLaw M omega x := by
  have := hQ.1 x
  obtain ⟨C, -, hC⟩ := exists_bound_isResolventTest hf
  refine LaplaceUniqueness.eq_of_integral_exp_neg_mul_eq (B := C)
    (continuous_pathIntegral (Q x) hf.1 hC)
    (continuous_pathIntegral (liveLaw M omega x) hf.1 hC)
    (abs_pathIntegral_le (Q x) hC) (abs_pathIntegral_le (liveLaw M omega x) hC)
    (fun lam hlam => integral_exp_neg_mul_eq_of_isDiffusionOf M omega Q hQ hf x hlam) ht

/-! ## 5. The marginals and the displays -/

/-- **Work item D.**  The time-`t` marginal of any diffusion of the stream
field is the time-`t` marginal of the live stream law: the two agree on the
nonnegative continuous compactly supported functions, hence on all of them,
hence as measures. -/
theorem map_eval_eq_liveLaw (Q : Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : IsDiffusionOf (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega) Q)
    (x : Vec d) {t : ℝ} (ht : 0 < t) :
    Measure.map (fun path : ContinuousPath (Vec d) => path t.toNNReal) (Q x) =
      Measure.map (fun path : ContinuousPath (Vec d) => path t.toNNReal)
        (liveLaw M omega x) := by
  have := hQ.1 x
  have hevm : Measurable fun path : ContinuousPath (Vec d) => path t.toNNReal :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t.toNNReal
  have : IsProbabilityMeasure
      (Measure.map (fun path : ContinuousPath (Vec d) => path t.toNNReal) (Q x)) :=
    Measure.isProbabilityMeasure_map hevm.aemeasurable
  have : IsProbabilityMeasure
      (Measure.map (fun path : ContinuousPath (Vec d) => path t.toNNReal)
        (liveLaw M omega x)) := Measure.isProbabilityMeasure_map hevm.aemeasurable
  have hnonneg : ∀ psi : Vec d → ℝ, Continuous psi → HasCompactSupport psi →
      (∀ y, 0 ≤ psi y) →
      (∫ y, psi y ∂Measure.map (fun path : ContinuousPath (Vec d) => path t.toNNReal) (Q x)) =
        ∫ y, psi y ∂Measure.map (fun path : ContinuousPath (Vec d) => path t.toNNReal)
          (liveLaw M omega x) := by
    intro psi hc hs h0
    rw [integral_map hevm.aemeasurable hc.aestronglyMeasurable,
      integral_map hevm.aemeasurable hc.aestronglyMeasurable]
    exact integral_eval_eq_of_isDiffusionOf M omega Q hQ ⟨hc, hs, h0⟩ x ht
  refine Measure.ext_of_integral_eq_on_compactlySupported fun phi => ?_
  obtain ⟨C, -, hC⟩ := exists_bound_of_hasCompactSupport phi.continuous phi.hasCompactSupport
  set p : Vec d → ℝ := fun y => max (phi y) 0 with hp
  set n : Vec d → ℝ := fun y => max (-phi y) 0 with hn
  have hpc : Continuous p := phi.continuous.max continuous_const
  have hnc : Continuous n := phi.continuous.neg.max continuous_const
  have hps : HasCompactSupport p := by
    refine phi.hasCompactSupport.mono fun y hy => ?_
    simp only [hp, Function.mem_support, ne_eq] at hy ⊢
    intro hzero
    exact hy (by rw [hzero]; simp)
  have hns : HasCompactSupport n := by
    refine phi.hasCompactSupport.mono fun y hy => ?_
    simp only [hn, Function.mem_support, ne_eq] at hy ⊢
    intro hzero
    exact hy (by rw [hzero]; simp)
  have hsplit : ∀ y, phi y = p y - n y := by
    intro y
    simp only [hp, hn]
    rcases le_total (phi y) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hpC : ∀ y, |p y| ≤ C := fun y => by
    rw [hp, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hC y)) ((abs_nonneg _).trans (hC y))
  have hnC : ∀ y, |n y| ≤ C := fun y => by
    rw [hn, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((neg_le_abs _).trans (hC y)) ((abs_nonneg _).trans (hC y))
  have hsub : ∀ mu : Measure (Vec d), IsFiniteMeasure mu →
      (∫ y, phi y ∂mu) = (∫ y, p y ∂mu) - ∫ y, n y ∂mu := by
    intro mu hmu
    have := hmu
    rw [← integral_sub (integrable_of_bounded hpc hpC) (integrable_of_bounded hnc hnC)]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  rw [hsub _ inferInstance, hsub _ inferInstance,
    hnonneg p hpc hps (fun y => le_max_right _ _),
    hnonneg n hnc hns (fun y => le_max_right _ _)]

/-- The display transfer: an observable of the position at a positive time,
read through any diffusion of the stream field, is the same observable read
through the compactified process of the repository. -/
theorem integral_eval_eq_streamProcess {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : IsDiffusionOf (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega) Q)
    (x : Vec d) {t : ℝ} (ht : 0 < t) {G : Vec d → E} (hG : Continuous G) :
    letI := (streamReg M omega).metricSpace
    letI := (streamReg M omega).completeSpace
    (∫ path, G (path t.toNNReal) ∂Q x) =
      ∫ path, G (onePointRetract (0 : Vec d) (path t.toNNReal))
        ∂streamProcess M omega (x : OnePoint (Vec d)) := by
  let := (streamReg M omega).metricSpace
  let := (streamReg M omega).completeSpace
  have hevm : Measurable fun path : ContinuousPath (Vec d) => path t.toNNReal :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t.toNNReal
  have hstep : (∫ path, G (path t.toNNReal) ∂Q x) =
      ∫ path, G (path t.toNNReal) ∂liveLaw M omega x := by
    rw [← integral_map hevm.aemeasurable hG.aestronglyMeasurable,
      map_eval_eq_liveLaw M omega Q hQ x ht,
      integral_map hevm.aemeasurable hG.aestronglyMeasurable]
  have hmeas : AEStronglyMeasurable
      (fun path : ContinuousPath (OnePoint (Vec d)) =>
        G (onePointRetract (0 : Vec d) (path t.toNNReal)))
      (streamProcess M omega (x : OnePoint (Vec d))) :=
    (hG.measurable.comp ((measurable_onePointRetract (0 : Vec d)).comp
      (ContinuousPath.measurable_coordinateProcess
        (alpha := OnePoint (Vec d)) t.toNNReal))).aestronglyMeasurable
  rw [hstep, ← integral_liveLaw M omega x
    (fun path => G (onePointRetract (0 : Vec d) (path t.toNNReal))) hmeas]
  rfl

end

end SuperdiffusionAudit.Support.SDMarginal
