import SuperdiffusionAudit.Support.SuperdiffusivityMarginal
import Algsuperdiff.Section5.Provider.EarlyExitScaleMoments
import Algsuperdiff.Section5.Provider.PthMomentProcess

/-!
# Integrability of the displacement observables

The confinement-scale tail gives finite first and second moments of the
constructed process. Equality of one-time marginals transfers integrability
to every path-law family satisfying the challenge's diffusion characterization.
-/

namespace SuperdiffusionAudit.Support.SDIntegrability

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open Algsuperdiff.Section5.Provider
open DivergenceFormProcess.Form DivergenceFormProcess.LiveRestriction
open Homogenization MarkovProcess MeasureTheory
open SuperdiffusionAudit.Support.SDLiveLaw SuperdiffusionAudit.Support.SDMarginal
open scoped ENNReal NNReal

noncomputable section

/-- A small-coupling threshold, chosen before the model and time, at which
the constructed process has every positive real moment of order at least one. -/
theorem exists_ae_integrable_streamProcess_norm_rpow
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gammaI : ℝ, 0 < gammaI ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gammaI →
      ∀ t : ℝ, 0 < t →
      ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
        let := (streamReg M omega).metricSpace
        let := (streamReg M omega).completeSpace
        ∀ p : ℝ, 1 ≤ p →
          Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
            ‖onePointRetract (0 : Vec d) (path t.toNNReal)‖ ^ p)
            (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) := by
  obtain ⟨gammaI, Cscale, CSbar, Kbar, cbar, hgammaI, _hCscale, _hCSbar, _hKbar,
    hcbar, hcbar1, hlift⟩ :=
    measureReal_compl_survivalEvent_confinementScale_le_pow_of_threshold_with_scaleMomentRange
      d hd cstar hcstar
  refine ⟨gammaI, hgammaI, ?_⟩
  intro M hcs hgamma t ht
  obtain ⟨S, K, L, c, CS, pS, _hK, _hKmin, _hc, _hc1, _hcbarle, _hL, _hSform,
    _hSmeas, _hSnn, _hCS, _hpS, _hCSle, _hKle, _hpSrange, _hSmom, _hconf, _hearly,
    _hdispk, _hdispR, htail⟩ := hlift M hcs hgamma t ht 1
  filter_upwards [htail] with omega homega
  let := (streamReg M omega).metricSpace
  let := (streamReg M omega).completeSpace
  intro p hp
  exact (integral_norm_onePointRetract_streamProcess_rpow_le_of_triadic_sq_tail
    M omega t.toNNReal
    (zpow_pos (by norm_num : (0 : ℝ) < 3) (confinementScale S L omega.1))
    hcbar hcbar1 hp homega).1

/-- Integrability transfers through the live-path embedding and equality of
the characterized one-time marginals; no equality of totalized integrals is used. -/
theorem integrable_eval_of_streamProcess
    {d : ℕ} [NeZero d] (M : ABKModel d) (omega : FullSample d M.gamma)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : Algsuperdiff.StatementAudit.Superdiffusivity.HasDiffusionMarginals
      (streamCoefficient M.nu omega) Q)
    (x : Vec d) {t : ℝ} (ht : 0 < t) {G : Vec d → E} (hG : Continuous G) :
    let := (streamReg M omega).metricSpace
    let := (streamReg M omega).completeSpace
    Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
      G (onePointRetract (0 : Vec d) (path t.toNNReal)))
      (streamProcess M omega (x : OnePoint (Vec d))) →
    Integrable (fun path : ContinuousPath (Vec d) => G (path t.toNNReal)) (Q x) := by
  let := (streamReg M omega).metricSpace
  let := (streamReg M omega).completeSpace
  dsimp only
  intro hInt
  rw [← map_pathPostcomp_liveLaw M omega x] at hInt
  have hLive := hInt.comp_measurable
    (measurableEmbedding_pathPostcomp (Y := OnePoint (Vec d)) injective_liveCoe).measurable
  have hLive' : Integrable (fun path : ContinuousPath (Vec d) => G (path t.toNNReal))
      (liveLaw M omega x) := by
    simpa only [Function.comp_def, pathPostcomp_apply, liveEmbedding_apply,
      onePointRetract_coe] using hLive
  have hev : Measurable (fun path : ContinuousPath (Vec d) => path t.toNNReal) :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t.toNNReal
  apply (integrable_map_measure (μ := Q x) hG.aestronglyMeasurable hev.aemeasurable).mp
  rw [map_eval_eq_liveLaw M omega Q hQ x ht]
  exact (integrable_map_measure hG.aestronglyMeasurable hev.aemeasurable).mpr hLive'

/-- First and second displacement moments of every characterized diffusion are
finite whenever the constructed process has finite norm moments. -/
theorem integrable_displacement_of_streamProcess
    {d : ℕ} [NeZero d] (M : ABKModel d) (omega : FullSample d M.gamma)
    (Q : Vec d → Measure (ContinuousPath (Vec d)))
    (hQ : Algsuperdiff.StatementAudit.Superdiffusivity.HasDiffusionMarginals
      (streamCoefficient M.nu omega) Q)
    {t : ℝ} (ht : 0 < t) :
    (let := (streamReg M omega).metricSpace
     let := (streamReg M omega).completeSpace
     ∀ p : ℝ, 1 ≤ p →
       Integrable (fun path : ContinuousPath (OnePoint (Vec d)) =>
         ‖onePointRetract (0 : Vec d) (path t.toNNReal)‖ ^ p)
         (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d)))) →
    Integrable (fun path => path t.toNNReal) (Q 0) ∧
    Integrable (fun path => vecNormSq (path t.toNNReal)) (Q 0) := by
  let := (streamReg M omega).metricSpace
  let := (streamReg M omega).completeSpace
  dsimp only
  intro hfinite
  have hnorm : Integrable (fun path => ‖path t.toNNReal‖) (Q 0) := by
    apply integrable_eval_of_streamProcess M omega Q hQ 0 ht continuous_norm
    simpa only [Real.rpow_one] using hfinite 1 le_rfl
  have hsq : Integrable (fun path => ‖path t.toNNReal‖ ^ (2 : ℕ)) (Q 0) := by
    apply integrable_eval_of_streamProcess M omega Q hQ 0 ht (continuous_norm.pow 2)
    simpa only [Pi.pow_apply, Real.rpow_two] using hfinite 2 (by norm_num)
  have hev : Measurable (fun path : ContinuousPath (Vec d) => path t.toNNReal) :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t.toNNReal
  refine ⟨(integrable_norm_iff hev.aestronglyMeasurable).mp hnorm, ?_⟩
  have hcont : Continuous (vecNormSq (d := d)) := by
    unfold vecNormSq vecDot
    fun_prop
  apply (hsq.const_mul (d : ℝ)).mono' (hcont.measurable.comp hev).aestronglyMeasurable
  filter_upwards [] with path
  change ‖vecNormSq (path t.toNNReal)‖ ≤ (d : ℝ) * ‖path t.toNNReal‖ ^ (2 : ℕ)
  rw [Real.norm_of_nonneg (vecNormSq_nonneg _)]
  let v := path t.toNNReal
  change vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ (2 : ℕ)
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hi : |v i| ≤ ‖v‖ := norm_le_pi_norm v i
      calc
        v i * v i = |v i| ^ (2 : ℕ) := by
          rw [pow_two, ← abs_mul, abs_mul_self]
        _ ≤ ‖v‖ ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ = (d : ℝ) * ‖v‖ ^ (2 : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end SuperdiffusionAudit.Support.SDIntegrability
