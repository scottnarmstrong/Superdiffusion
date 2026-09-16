import SuperdiffusionAudit.Support.StreamCubeResolventMeasurable
import SuperdiffusionAudit.Support.StreamResolventMeasurable
import SuperdiffusionAudit.Support.SuperdiffusivityTransition

/-!
# Measurable quenched displacement expectations

The full stream's cube resolvents depend measurably on the environment.
Countable exhaustion and semigroup generation give measurable transition laws;
the diffusion characterization transfers this to every admissible family.
-/

namespace SuperdiffusionAudit.Support.SDMeasurability

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open Algsuperdiff.StatementAudit.Superdiffusivity
open Homogenization MarkovProcess MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d] (M : ABKModel d)

private theorem measurable_fixed_second {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {F : Ω × X → Y} (hF : Measurable F) (x : X) :
    Measurable fun omega => F (omega, x) :=
  hF.comp (measurable_id.prodMk measurable_const)

theorem measurable_streamTransition (t : NNReal) :
    Measurable fun p : Algsuperdiff.Section5.Field.FullSample d M.gamma × Homogenization.Vec d =>
      (streamWholeSpaceResolvent M p.1).kernelSemigroup t p.2 :=
  measurable_streamTransition_of_cube M (measurable_analyticCubeResolvent_stream M) t

theorem measurable_integral_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Algsuperdiff.Section5.Field.FullSample d M.gamma →
      Homogenization.Vec d → Measure (ContinuousPath (Homogenization.Vec d)))
    (hQ : ∀ omega, IsDiffusionOf
      (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega) (Q omega))
    (x : Homogenization.Vec d) {t : ℝ} (ht : 0 < t)
    {G : Homogenization.Vec d → E} (hG : Continuous G) :
    Measurable fun omega => ∫ path, G (path t.toNNReal) ∂Q omega x := by
  have htransition : Measurable fun omega : Algsuperdiff.Section5.Field.FullSample d M.gamma =>
      (streamWholeSpaceResolvent M omega).kernelSemigroup t.toNNReal x :=
    measurable_fixed_second (measurable_streamTransition M t.toNNReal) x
  exact SDTransition.measurable_integral_eval_of_measurable_transition M Q hQ x ht
    htransition hG

end
end SuperdiffusionAudit.Support.SDMeasurability
