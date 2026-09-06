import Mathlib
import Algsuperdiff.MainTheorems
import SuperdiffusionAudit.Support.SuperdiffusivityBridge

/-!
# The cube resolvents of the challenge are the analytic cube resolvents

The `Superdiffusivity` challenge characterizes the diffusion of a coefficient
field through the family of *cube resolvents*: functions continuous on an
exhaustion cube, zero outside it, and almost everywhere equal on the cube to a
zero-trace weak solution of `lam u - ∇·a∇u = f` (`IsCubeResolvent`).  This file
supplies the repository's `analyticCubeResolvent` as such a witness and
computes the supremum of the family.

1.  the weak equation: the abstract `IsAlphaShiftedWeakSolution` of the
    divergence-form foundation is the challenge's `IsResolventSolutionOn`,
    once the two inner products and the coefficient pairing are written as
    explicit set integrals (the pattern of
    `Algsuperdiff/StochasticProcess/Common/DivergenceForm/InteriorEquationBridge.lean`);
2.  `isCubeResolvent_analyticCubeResolvent`: the zero-extended analytic
    Dirichlet resolvent of the cube is a cube resolvent;
3.  `iSup_analyticCubeResolvent`: its supremum over the exhaustion is the real
    form of the analytic minimal resolvent;
4.  `isCubeResolvent_unique`: a cube resolvent is unique, so the challenge's
    universally quantified family is the analytic one.
-/

namespace SuperdiffusionAudit.Support.SDResolvent

open Algsuperdiff.StatementAudit.Superdiffusivity
open DivergenceFormProcess.Form MarkovProcess.Semigroup MeasureTheory
open SuperdiffusionAudit.Support.SDBridge
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-! ## 1. Inner products as set integrals -/

theorem inner_toScalarL2 {U : Set (Vec d)} (u v : Homogenization.H1Function U) :
    ⟪u.toScalarL2, v.toScalarL2⟫ = ∫ x in U, u.toFun x * v.toFun x ∂volume := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [u.coeFn_toScalarL2, v.coeFn_toScalarL2] with x h1 h2
  rw [h1, h2, RCLike.inner_apply']
  simp

theorem inner_boundedMeasurableToScalarL2 {U : Set (Vec d)}
    (hU : Homogenization.IsOpenBoundedConvexDomain U) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (v : Homogenization.H1Function U) :
    ⟪boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y => hfD y),
        v.toScalarL2⟫ = ∫ x in U, f x * v.toFun x ∂volume := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU (hf.comp measurable_subtype_coe)
      (fun y => hfD y), v.coeFn_toScalarL2, ae_restrict_mem hU.isOpen.measurableSet]
    with x h1 h2 hx
  rw [h1, h2, RCLike.inner_apply', domainExtension_of_mem hx]
  simp

theorem coefficientPairing_eq_setIntegral {U : Set (Vec d)} (a : Homogenization.CoeffField d)
    (u v : Homogenization.H1Function U) :
    coefficientPairing a U u.gradToHilbertVectorL2 v.gradToHilbertVectorL2 =
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (v.grad x) ∂volume := by
  rw [coefficientPairing]
  refine integral_congr_ae ?_
  filter_upwards [Homogenization.coeFn_hilbertVectorL2ToVectorL2 (U := U) u.gradToHilbertVectorL2,
    Homogenization.coeFn_hilbertVectorL2ToVectorL2 (U := U) v.gradToHilbertVectorL2,
    u.coeFn_gradToHilbertVectorL2, v.coeFn_gradToHilbertVectorL2] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp only [Homogenization.hilbertifyVecField]
  rfl

/-! ## 2. The weak equation -/

/-- The abstract zero-trace weak equation of the divergence-form foundation is
the challenge's `IsResolventSolutionOn`. -/
theorem isResolventSolutionOn_of_isAlphaShiftedWeakSolution [NeZero d]
    {U : Set (Vec d)} (hU : Homogenization.IsOpenBoundedConvexDomain U)
    (a : Homogenization.CoeffField d) {lam : ℝ}
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (u : Homogenization.H10Function U)
    (hu : IsAlphaShiftedWeakSolution a U lam
      (boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y => hfD y))
      (ZeroTraceSobolev.ofH10Function u)) :
    IsResolventSolutionOn a U lam f (ofRepoH10 u) := by
  intro phi
  have hphi := hu (ZeroTraceSobolev.ofH10Function (toRepoH10 phi))
  rw [ZeroTraceSobolev.toL2_ofH10Function, ZeroTraceSobolev.toL2_ofH10Function,
    ZeroTraceSobolev.gradient_ofH10Function, ZeroTraceSobolev.gradient_ofH10Function,
    inner_toScalarL2, coefficientPairing_eq_setIntegral,
    inner_boundedMeasurableToScalarL2 hU hf hfD] at hphi
  exact hphi

/-! ## 3. The analytic cube resolvent is a cube resolvent -/

variable [NeZero d]

theorem analyticCubeResolvent_of_notMem (A : WholeSpaceAnalyticData d) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ)
    {x : Vec d} (hx : x ∉ DivergenceFormProcess.Form.wholeSpaceCube d m) :
    A.analyticCubeResolvent mu f hf hfD m x = 0 := by
  rw [WholeSpaceAnalyticData.analyticCubeResolvent, dif_neg hx]

omit [NeZero d] in
/-- The challenge's cube-resolvent predicate, transported from the
repository's exhaustion cube.  The two cubes are equal as sets, not
definitionally, so the zero-trace witness is carried across explicitly. -/
theorem isCubeResolvent_of_repo {a : Homogenization.CoeffField d} {lam : ℝ}
    {f : Vec d → ℝ} {m : ℕ} {v : Vec d → ℝ}
    (hcont : ContinuousOn v (DivergenceFormProcess.Form.wholeSpaceCube d m))
    (hzero : ∀ x ∉ DivergenceFormProcess.Form.wholeSpaceCube d m, v x = 0)
    (u : Homogenization.H10Function (DivergenceFormProcess.Form.wholeSpaceCube d m))
    (hsol : IsResolventSolutionOn a (DivergenceFormProcess.Form.wholeSpaceCube d m) lam f
      (ofRepoH10 u))
    (hae : ∀ᵐ x ∂(volume.restrict (DivergenceFormProcess.Form.wholeSpaceCube d m)),
      u.toH1Function.toFun x = v x) :
    IsCubeResolvent a lam f m v := by
  unfold IsCubeResolvent
  rw [wholeSpaceCube_eq d m]
  exact ⟨hcont, hzero, ofRepoH10 u, hsol, hae⟩

/-- **Work item A.**  The zero-extended analytic Dirichlet resolvent of the
`m`th exhaustion cube satisfies the challenge's characterization of a cube
resolvent. -/
theorem isCubeResolvent_analyticCubeResolvent (A : WholeSpaceAnalyticData d)
    {lam : ℝ} (hlam : 0 < lam) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    IsCubeResolvent A.a lam f m (A.analyticCubeResolvent ⟨lam, hlam⟩ f hf hfD m) := by
  set mu : PositiveShift := ⟨lam, hlam⟩ with hmu
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  obtain ⟨u, -, hweak, hrep⟩ :=
    exists_h10Function_alphaShiftedResolvent hU A.a hlam A.hnu (A.cubeEllipticity m)
      (boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y => hfD y))
  refine isCubeResolvent_of_repo (A.continuousOn_analyticCubeResolvent mu hf hfD m)
    (fun x hx => analyticCubeResolvent_of_notMem A mu hf hfD m hx) u
    (isResolventSolutionOn_of_isAlphaShiftedWeakSolution hU A.a hf hfD u hweak) ?_
  filter_upwards [u.toH1Function.coeFn_toScalarL2,
    A.analyticCubeResolvent_ae mu hf hfD m] with x h1 h2
  rw [← h1, hrep, ← h2]

/-! ## 4. The supremum along the exhaustion -/

/-- **Work item B.**  The supremum of the analytic cube resolvents of a
nonnegative datum is the real form of the analytic minimal resolvent. -/
theorem iSup_analyticCubeResolvent (A : WholeSpaceAnalyticData d) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    (⨆ m, A.analyticCubeResolvent mu f hf hfD m x) =
      (A.analyticMinimalResolvent mu f hf hfD x).toReal := by
  set c : ℕ → ℝ := fun m => A.analyticCubeResolvent mu f hf hfD m x with hc
  have hmono : Monotone c := A.monotone_analyticCubeResolvent mu hf hf0 hfD x
  have hbdd : BddAbove (Set.range c) := by
    refine ⟨D / (mu : ℝ), ?_⟩
    rintro _ ⟨m, rfl⟩
    exact (le_abs_self _).trans (A.abs_analyticCubeResolvent_le mu hf hD hfD m x)
  have hnonneg : 0 ≤ ⨆ m, c m :=
    le_ciSup_of_le hbdd 0 (A.analyticCubeResolvent_nonneg mu hf hf0 hfD 0 x)
  have htend : Filter.Tendsto c Filter.atTop (nhds (⨆ m, c m)) := tendsto_atTop_ciSup hmono hbdd
  have htendE : Filter.Tendsto (fun m => ENNReal.ofReal (c m)) Filter.atTop
      (nhds (ENNReal.ofReal (⨆ m, c m))) := (ENNReal.continuous_ofReal.tendsto _).comp htend
  have hmonoE : Monotone fun m => ENNReal.ofReal (c m) :=
    fun i j hij => ENNReal.ofReal_le_ofReal (hmono hij)
  have hsup : A.analyticMinimalResolvent mu f hf hfD x = ENNReal.ofReal (⨆ m, c m) := by
    refine tendsto_nhds_unique ?_ htendE
    exact tendsto_atTop_iSup hmonoE
  rw [hsup, ENNReal.toReal_ofReal hnonneg]

/-! ## 5. Uniqueness of the cube resolvent -/

/-- The converse of §2: the challenge's `IsResolventSolutionOn` is the abstract
zero-trace weak equation.  Every zero-trace element has an `H¹₀` representative,
so the challenge's test quantifier is not weaker. -/
theorem isAlphaShiftedWeakSolution_of_isResolventSolutionOn
    {U : Set (Vec d)} (hU : Homogenization.IsOpenBoundedConvexDomain U)
    (a : Homogenization.CoeffField d) {lam : ℝ}
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (u : H10Function U) (hu : IsResolventSolutionOn a U lam f u) :
    IsAlphaShiftedWeakSolution a U lam
      (boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y => hfD y))
      (ZeroTraceSobolev.ofH10Function (toRepoH10 u)) := by
  intro z
  obtain ⟨phi, hval, hgrad⟩ := ZeroTraceSobolev.exists_h10Function hU z
  have hz : ZeroTraceSobolev.ofH10Function phi = z := by
    refine ZeroTraceSobolev.ext ?_ ?_
    · rw [ZeroTraceSobolev.toL2_ofH10Function, hval]
    · rw [ZeroTraceSobolev.gradient_ofH10Function, hgrad]
  rw [← hz, ZeroTraceSobolev.toL2_ofH10Function, ZeroTraceSobolev.toL2_ofH10Function,
    ZeroTraceSobolev.gradient_ofH10Function, ZeroTraceSobolev.gradient_ofH10Function,
    inner_toScalarL2, coefficientPairing_eq_setIntegral,
    inner_boundedMeasurableToScalarL2 hU hf hfD]
  exact hu (ofRepoH10 phi)

/-- **Uniqueness of the cube resolvent.**  Continuity on the open cube pins the
`H¹₀` solution pointwise, and the solution itself is unique, so the challenge's
universally quantified cube-resolvent family is the analytic one. -/
theorem eq_analyticCubeResolvent_of_isCubeResolvent (A : WholeSpaceAnalyticData d)
    {lam : ℝ} (hlam : 0 < lam) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) {w : Vec d → ℝ}
    (hw : IsCubeResolvent A.a lam f m w) :
    w = A.analyticCubeResolvent ⟨lam, hlam⟩ f hf hfD m := by
  set mu : PositiveShift := ⟨lam, hlam⟩ with hmu
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  set fL2 := boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y => hfD y)
    with hfL2
  unfold IsCubeResolvent at hw
  rw [wholeSpaceCube_eq d m] at hw
  obtain ⟨hcont, hzero, u, hsol, hae⟩ := hw
  obtain ⟨u0, -, hweak0, hrep0⟩ :=
    exists_h10Function_alphaShiftedResolvent hU A.a hlam A.hnu (A.cubeEllipticity m) fL2
  have huniq := existsUnique_isAlphaShiftedWeakSolution A.a hlam A.hnu (A.cubeEllipticity m) fL2
  have heqZ : ZeroTraceSobolev.ofH10Function (toRepoH10 u) =
      ZeroTraceSobolev.ofH10Function u0 := by
    obtain ⟨_, _, hune⟩ := huniq
    rw [hune _ (isAlphaShiftedWeakSolution_of_isResolventSolutionOn hU A.a hf hfD u hsol),
      hune _ hweak0]
  have heqL2 : (toRepoH10 u).toH1Function.toScalarL2 = u0.toH1Function.toScalarL2 := by
    have := congrArg ZeroTraceSobolev.toL2 heqZ
    rwa [ZeroTraceSobolev.toL2_ofH10Function, ZeroTraceSobolev.toL2_ofH10Function] at this
  have haeCube : ∀ᵐ x ∂(volume.restrict (DivergenceFormProcess.Form.wholeSpaceCube d m)),
      w x = A.analyticCubeResolvent mu f hf hfD m x := by
    filter_upwards [hae, (toRepoH10 u).toH1Function.coeFn_toScalarL2,
      u0.toH1Function.coeFn_toScalarL2, A.analyticCubeResolvent_ae mu hf hfD m]
      with x h1 h2 h3 h4
    have e1 : w x = ((toRepoH10 u).toH1Function.toScalarL2 : Vec d → ℝ) x := by
      rw [← h1]
      exact h2.symm
    have e2 : ((u0.toH1Function.toScalarL2 : Vec d → ℝ)) x =
        A.analyticCubeResolvent mu f hf hfD m x := by
      rw [hrep0]
      exact h4.symm
    rw [e1, heqL2, e2]
  have heqOn : Set.EqOn w (A.analyticCubeResolvent mu f hf hfD m)
      (DivergenceFormProcess.Form.wholeSpaceCube d m) :=
    Measure.eqOn_open_of_ae_eq haeCube
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen hcont
      (A.continuousOn_analyticCubeResolvent mu hf hfD m)
  funext x
  by_cases hx : x ∈ DivergenceFormProcess.Form.wholeSpaceCube d m
  · exact heqOn hx
  · rw [hzero x hx, analyticCubeResolvent_of_notMem A mu hf hfD m hx]

end

end SuperdiffusionAudit.Support.SDResolvent
