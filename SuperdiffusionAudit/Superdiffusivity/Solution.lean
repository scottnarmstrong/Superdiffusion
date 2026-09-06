import Mathlib
import Algsuperdiff.MainTheorems
import SuperdiffusionAudit.Superdiffusivity.SolutionBasic
import SuperdiffusionAudit.Support.SuperdiffusivityBridge
import SuperdiffusionAudit.Support.SuperdiffusivityMarginal

/-!
# Solution: Superdiffusivity

The challenge module `SuperdiffusionAudit/Superdiffusivity/Challenge.lean` imports only Mathlib
and states the theorem with one intentional `sorry`.  This solution imports the
repository together with `SuperdiffusionAudit.Superdiffusivity.SolutionBasic` — a verbatim copy
of the challenge's statement vocabulary — and proves the audited theorem with a
byte-identical statement, through the bridges in `SuperdiffusionAudit/Support/`.
-/

namespace Algsuperdiff
namespace StatementAudit
namespace Superdiffusivity

open SuperdiffusionAudit.Support.SDBridge
open SuperdiffusionAudit.Support.SDLiveLaw
open SuperdiffusionAudit.Support.SDMarginal
open MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.Elementwise

noncomputable section

/-- The squared Euclidean length is continuous. -/
private theorem continuous_vecNormSq (d : ℕ) : Continuous (vecNormSq (d := d)) := by
  unfold vecNormSq vecDot
  fun_prop

/-- The annealed lower integral of the challenge is the annealed lower integral
of the repository, at the transported model.  Stated for a variable integrand:
the conversion of the carrier and of the law is then performed once, away from
the displays. -/
private theorem lintegral_fullSampleMeasure {d : ℕ} (m : Model d)
    (F : FullSample d m.gamma → ℝ≥0∞) :
    (∫⁻ om, F om ∂fullSampleMeasure m.gamma m.P) =
      ∫⁻ om : _root_.Algsuperdiff.Section5.Field.FullSample d (toABKModel m).gamma, F om
        ∂(_root_.Algsuperdiff.Section5.Field.fullSampleLaw (toABKModel m)).toMeasure := rfl

theorem superdiffusivity
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : Model d, RealizesCstar d M.P cstar → M.gamma ≤ gamma0 →
        (∀ omega : FullSample d M.gamma,
            ∃ Q : Vec d → Measure C(ℝ≥0, Vec d),
              IsDiffusionOf (streamCoefficient M.nu omega) Q) ∧
        ∀ Q : FullSample d M.gamma → Vec d → Measure C(ℝ≥0, Vec d),
          (∀ omega, IsDiffusionOf (streamCoefficient M.nu omega) (Q omega)) →
          ∀ t : ℝ, 0 < t →
          ∀ p : ℝ, 1 ≤ p →
            p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) →
            (∫⁻ omega : FullSample d M.gamma,
                ENNReal.ofReal
                    |(∫ path, vecNormSq (path t.toNNReal) ∂Q omega 0) -
                      2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ^ p
                ∂fullSampleMeasure M.gamma M.P) ≤
              ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                  Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
                  intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p ∧
            (∫⁻ omega : FullSample d M.gamma,
                ENNReal.ofReal
                    (vecNormSq (∫ path, path t.toNNReal ∂Q omega 0)) ^ p
                ∂fullSampleMeasure M.gamma M.P) ≤
              ENNReal.ofReal (C * (p + |Real.log M.gamma|) * M.gamma *
                  |Real.log M.gamma| ^ (7 : ℕ) *
                  intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M
    exact absurd M.dimension (by omega)
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨gamma0, C, hgamma0, hC, hmain⟩ :=
    _root_.Algsuperdiff.superdiffusivity d cstar _hcstar
  refine ⟨gamma0, C, hgamma0, hC, ?_⟩
  intro M hreal hgamma
  have hcs : _root_.Algsuperdiff.Section3.Disorder.cstar (toABKModel M) = cstar :=
    (realizesCstar_iff_cstar_eq (toABKModel M) _hcstar).mp hreal
  refine ⟨fun om => ⟨liveLaw (toABKModel M) om, isDiffusionOf_liveLaw (toABKModel M) om⟩, ?_⟩
  intro Q hQ t ht p hp1 hp2
  obtain ⟨hone, htwo⟩ := hmain (toABKModel M) hcs hgamma t ht p hp1 hp2
  have hsq : ∀ om : _root_.Algsuperdiff.Section5.Field.FullSample d (toABKModel M).gamma,
      (∫ path, vecNormSq (path t.toNNReal) ∂Q om 0) =
        letI := (SuperdiffusionAudit.Support.SDLiveLaw.streamReg (toABKModel M) om).metricSpace
        letI := (SuperdiffusionAudit.Support.SDLiveLaw.streamReg (toABKModel M) om).completeSpace
        ∫ path, vecNormSq (DivergenceFormProcess.Form.onePointRetract (0 : Vec d)
            (path t.toNNReal))
          ∂((_root_.Algsuperdiff.Section5.Field.streamExhaustionTailInput (toABKModel M) om
            ).wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))) := fun om =>
    integral_eval_eq_streamProcess (toABKModel M) om (Q om) (hQ om) 0 ht (continuous_vecNormSq d)
  have hpos : ∀ om : _root_.Algsuperdiff.Section5.Field.FullSample d (toABKModel M).gamma,
      (∫ path, path t.toNNReal ∂Q om 0) =
        letI := (SuperdiffusionAudit.Support.SDLiveLaw.streamReg (toABKModel M) om).metricSpace
        letI := (SuperdiffusionAudit.Support.SDLiveLaw.streamReg (toABKModel M) om).completeSpace
        ∫ path, DivergenceFormProcess.Form.onePointRetract (0 : Vec d) (path t.toNNReal)
          ∂((_root_.Algsuperdiff.Section5.Field.streamExhaustionTailInput (toABKModel M) om
            ).wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))) := fun om =>
    integral_eval_eq_streamProcess (toABKModel M) om (Q om) (hQ om) 0 ht continuous_id
  constructor
  · rw [lintegral_fullSampleMeasure M]
    refine le_trans (le_of_eq (lintegral_congr fun om => ?_)) hone
    rw [hsq om]
    rfl
  · rw [lintegral_fullSampleMeasure M]
    refine le_trans (le_of_eq (lintegral_congr fun om => ?_)) htwo
    rw [hpos om]
    rfl

end

end Superdiffusivity
end StatementAudit
end Algsuperdiff
