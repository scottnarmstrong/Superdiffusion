import SuperdiffusionAudit.Support.SuperdiffusivityMarginal

/-!
# Displacement expectations as transition-kernel integrals

The characterized diffusion has the same one-time expectations as the live
transition semigroup. This identity avoids choosing a common metric on the
environment-dependent compactifications.
-/

namespace SuperdiffusionAudit.Support.SDTransition

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open Algsuperdiff.StatementAudit.Superdiffusivity
open DivergenceFormProcess.Form
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MeasureTheory ProbabilityTheory
open SuperdiffusionAudit.Support.SDLiveLaw SuperdiffusionAudit.Support.SDMarginal

noncomputable section

variable {d : ℕ} [NeZero d] (M : ABKModel d)
  (omega : Algsuperdiff.Section5.Field.FullSample d M.gamma)

theorem integral_eval_eq_transition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : HasDiffusionMarginals (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega) Q)
    (x : Vec d) {t : ℝ} (ht : 0 < t) {G : Vec d → E} (hG : Continuous G) :
    (∫ path, G (path t.toNNReal) ∂Q x) =
      ∫ y, G y ∂(streamWholeSpaceResolvent M omega).kernelSemigroup t.toNNReal x := by
  let := (streamReg M omega).metricSpace
  let := (streamReg M omega).completeSpace
  let R := streamWholeSpaceResolvent M omega
  have hev : Measurable (fun path : ContinuousPath (OnePoint (Vec d)) => path t.toNNReal) :=
    ContinuousPath.measurable_coordinateProcess t.toNNReal
  have hret : StronglyMeasurable (fun y : OnePoint (Vec d) => G (onePointRetract (0 : Vec d) y)) :=
    (hG.measurable.comp (measurable_onePointRetract (0 : Vec d))).stronglyMeasurable
  have hmap : Measure.map (fun path : ContinuousPath (OnePoint (Vec d)) => path t.toNNReal)
      (streamProcess M omega (x : OnePoint (Vec d))) = R.onePointKernelSemigroup t.toNNReal x := by
    rw [streamProcess_eq M omega]
    have hk := R.isFellerKernelSemigroup_onePointKernelSemigroup.continuousProcess_map_eval_nnreal
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
      (streamReg M omega).kolmogorovRegular t.toNNReal
    exact (Kernel.map_apply _ hev (x : OnePoint (Vec d))).symm.trans
      (DFunLike.congr_fun hk (x : OnePoint (Vec d)))
  rw [integral_eval_eq_streamProcess M omega Q hQ x ht hG,
    ← integral_map hev.aemeasurable hret.aestronglyMeasurable, hmap,
    R.onePointKernelSemigroup_apply_coe]
  have hmass : R.kernelSemigroup t.toNNReal x Set.univ = 1 :=
    isConservative_streamKernelSemigroup M omega t.toNNReal x
  rw [hmass, tsub_self, zero_smul, add_zero,
    integral_map OnePoint.continuous_coe.measurable.aemeasurable hret.aestronglyMeasurable]
  rfl

omit omega in
/-- Measurability of transition measures transfers to expectations for every
family satisfying the diffusion characterization. -/
theorem measurable_integral_eval_of_measurable_transition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Algsuperdiff.Section5.Field.FullSample d M.gamma →
      Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : ∀ omega, HasDiffusionMarginals
      (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega) (Q omega))
    (x : Vec d) {t : ℝ} (ht : 0 < t)
    (htransition : Measurable fun omega : Algsuperdiff.Section5.Field.FullSample d M.gamma =>
      (streamWholeSpaceResolvent M omega).kernelSemigroup t.toNNReal x)
    {G : Vec d → E} (hG : Continuous G) :
    Measurable fun omega => ∫ path, G (path t.toNNReal) ∂Q omega x := by
  let K : Kernel (Algsuperdiff.Section5.Field.FullSample d M.gamma) (Vec d) :=
    ⟨fun omega => (streamWholeSpaceResolvent M omega).kernelSemigroup t.toNNReal x,
      htransition⟩
  have hK : Measurable fun omega => ∫ y, G y ∂K omega :=
    (hG.stronglyMeasurable.integral_kernel (κ := K)).measurable
  have heq : (fun omega => ∫ path, G (path t.toNNReal) ∂Q omega x) =
      (fun omega => ∫ y, G y ∂K omega) := by
    funext omega
    exact integral_eval_eq_transition M omega (Q omega) (hQ omega) x ht hG
  rw [heq]
  exact hK

end
end SuperdiffusionAudit.Support.SDTransition
