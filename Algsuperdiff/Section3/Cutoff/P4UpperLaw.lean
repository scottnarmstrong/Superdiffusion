import Algsuperdiff.Section3.Cutoff.P4UpperMoments

/-!
# Upper coarse-ellipticity moments under the cutoff law

This file transfers the independently proved samplewise cutoff envelope bound
and its Γ₂-derived polynomial moments through the literal cutoff pushforward.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Every finite upper coarse-ellipticity moment on an arbitrary deterministic
cube is integrable under the actual cutoff law. -/
theorem integrable_LambdaSqCoeffField_pow_cutoffLaw
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (xi : ℕ) :
    Integrable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField Q s (.finite 1) a) ^ xi)
      (coefficientCutoffLaw M m) := by
  let P := coefficientCutoffLaw M m
  let f : CutoffSample d → RegCoeffField d := coefficientCutoff M.nu m
  let C : ℝ := 4 * (d : ℝ) * M.nu⁻¹
  let L : CutoffSample d → ℝ := fun omega =>
    coefficientCutoffCubeEllipticityUpper M m omega Q
  let hP : Ch04.RestrictionLawCarrier P := coefficientCutoffLaw_lawCarrier M m
  have htarget_ae : AEMeasurable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField Q s (.finite 1) a) ^ xi) P :=
    (hP.aemeasurable_LambdaSqCoeffField_finite_one Q hs).pow_const xi
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le d))
      (inv_nonneg.mpr M.nu_pos.le)
  have hdom : Integrable (fun omega : CutoffSample d =>
      C ^ xi * L omega ^ (2 * xi)) (cutoffSampleLaw M).toMeasure := by
    have hL := integrable_coefficientCutoffCubeEllipticityUpper_pow M m Q (2 * xi)
    exact hL.const_mul (C ^ xi)
  change Integrable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField Q s (.finite 1) a) ^ xi) P
  rw [show P = Measure.map f (cutoffSampleLaw M).toMeasure by
    exact coefficientCutoffLaw_eq_map M m]
  apply (integrable_map_measure htarget_ae.aestronglyMeasurable
    (measurable_coefficientCutoff M.nu m).aemeasurable).mpr
  refine Integrable.mono' hdom
    (htarget_ae.comp_aemeasurable (measurable_coefficientCutoff M.nu m).aemeasurable).aestronglyMeasurable ?_
  filter_upwards with omega
  have hLambda_nonneg : 0 ≤ Ch04.LambdaSqCoeffField Q s (.finite 1) (f omega) :=
    Ch04.LambdaSqCoeffField_finite_nonneg Q (f omega) hs (by norm_num)
  have hL_nonneg : 0 ≤ L omega := by
    dsimp [L]
    unfold coefficientCutoffCubeEllipticityUpper
    apply div_nonneg
    · positivity
    · exact M.nu_pos.le
  have hbound : Ch04.LambdaSqCoeffField Q s (.finite 1) (f omega) ≤
      C * L omega ^ 2 := by
    simpa only [C, L, f] using LambdaSqCoeffField_le_cutoffEnvelope M m omega Q hs
  have hpw := pow_le_pow_left₀ hLambda_nonneg hbound xi
  have hright_nonneg : 0 ≤ C ^ xi * L omega ^ (2 * xi) := by positivity
  have hrewrite : (C * L omega ^ 2) ^ xi = C ^ xi * L omega ^ (2 * xi) := by
    rw [mul_pow, ← pow_mul]
  simpa only [Function.comp_apply, f, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hLambda_nonneg xi),
    abs_of_nonneg hright_nonneg, hrewrite] using hpw

end

end Algsuperdiff.Section3.Cutoff
