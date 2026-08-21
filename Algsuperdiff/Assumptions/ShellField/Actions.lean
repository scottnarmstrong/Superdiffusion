import Algsuperdiff.Assumptions.ShellField.Basic
import Algsuperdiff.Probability.RegCoeffFieldOperations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Exact transformations of regular shell fields

The actions in this module are the literal transformations used in ABK26:
amplitude scaling, real spatial translation, spatial scaling, triadic shell
scaling, negation, and signed-permutation conjugation.  Each transformation
acts on the stored first and second derivatives by the exact chain rule.
-/

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open Homogenization
open scoped Matrix.Norms.Elementwise

/-! ## Instance caches for the derivative carriers

The derivative carrier `Vec d →L[ℝ] Mat d` and the Hessian carrier
`Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)` are searched hundreds of times while
elaborating this file.  Caching the recurring classes once at module level
(outside the section, so that every declaration sees them) turns each search
into a single step.  Every cache below is literally the instance Lean would
otherwise rediscover.
-/

private noncomputable instance instTopDerivCarrier (d : ℕ) :
    TopologicalSpace (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instTopHessianCarrier (d : ℕ) :
    TopologicalSpace (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instAddCommMonoidDerivCarrier (d : ℕ) :
    AddCommMonoid (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instAddCommMonoidHessianCarrier (d : ℕ) :
    AddCommMonoid (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instSMulDerivCarrier (d : ℕ) :
    SMul ℝ (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instSMulHessianCarrier (d : ℕ) :
    SMul ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instModuleDerivCarrier (d : ℕ) :
    Module ℝ (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instModuleHessianCarrier (d : ℕ) :
    Module ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instNormedSpaceDerivCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instNormedSpaceHessianCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instNormedSpaceEndoCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] Vec d) := inferInstance

noncomputable section

variable {d : ℕ}

/-! ## Amplitude scaling -/

private def valueScaleMap (c : ℝ) : C(Mat d, Mat d) :=
  ⟨fun M ↦ c • M, continuous_id.const_smul c⟩

private def derivScaleMap (c : ℝ) :
    C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d) :=
  ⟨fun D ↦ c • D, continuous_id.const_smul c⟩

private def secondDerivScaleMap (c : ℝ) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨fun H ↦ c • H, continuous_id.const_smul c⟩

private def scaleAmbient (c : ℝ) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  ((valueScaleMap c).comp p.1,
    ((derivScaleMap c).comp p.2.1,
      (secondDerivScaleMap c).comp p.2.2))

private theorem continuous_scaleAmbient (c : ℝ) :
    Continuous (scaleAmbient (d := d) c) :=
  ((ContinuousMap.continuous_postcomp (valueScaleMap c)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (derivScaleMap c)).comp
      continuous_snd.fst).prodMk
        ((ContinuousMap.continuous_postcomp (secondDerivScaleMap c)).comp
          continuous_snd.snd))

/-- Multiply every matrix value by `c`. -/
def scale (c : ℝ) (j : ShellField d) : ShellField d :=
  ⟨scaleAmbient c j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simpa only [scaleAmbient, valueScaleMap, derivScaleMap,
        ContinuousMap.comp_apply] using (j.hasFDerivAt x).const_smul c
    · intro x
      simpa only [scaleAmbient, derivScaleMap, secondDerivScaleMap,
        ContinuousMap.comp_apply] using
        (j.deriv_hasFDerivAt x).const_smul c
    · intro x i k
      change c * j x i k = -(c * j x k i)
      rw [j.skew_entry x i k]
      ring⟩

@[simp]
theorem scale_apply (c : ℝ) (j : ShellField d) (x : Vec d) :
    scale c j x = c • j x :=
  rfl

@[simp]
theorem scale_deriv (c : ℝ) (j : ShellField d) (x : Vec d) :
    deriv (scale c j) x = c • deriv j x :=
  rfl

@[simp]
theorem scale_secondDeriv (c : ℝ) (j : ShellField d) (x : Vec d) :
    secondDeriv (scale c j) x = c • secondDeriv j x :=
  rfl

theorem continuous_scale (c : ℝ) :
    Continuous (scale (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_scaleAmbient c).comp continuous_subtype_val)
    (fun j ↦ (scale c j).2)

/-! ## Real spatial translations -/

private def translateMap (z : Vec d) : C(Vec d, Vec d) :=
  ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩

private def translateAmbient (z : Vec d) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  (p.1.comp (translateMap z),
    (p.2.1.comp (translateMap z), p.2.2.comp (translateMap z)))

private theorem continuous_translateAmbient (z : Vec d) :
    Continuous (translateAmbient (d := d) z) :=
  ((ContinuousMap.continuous_precomp (translateMap z)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_precomp (translateMap z)).comp
      continuous_snd.fst).prodMk
        ((ContinuousMap.continuous_precomp (translateMap z)).comp
          continuous_snd.snd))

/-- Real translation in the manuscript convention `j(x + z)`. -/
def translate (z : Vec d) (j : ShellField d) : ShellField d :=
  ⟨translateAmbient z j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply,
        Function.comp_def] using
        (j.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    · intro x
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply,
        Function.comp_def] using
        (j.deriv_hasFDerivAt (x + z)).comp x
          ((hasFDerivAt_id x).add_const z)
    · intro x i k
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply] using
        j.skew_entry (x + z) i k⟩

@[simp]
theorem translate_apply (z : Vec d) (j : ShellField d) (x : Vec d) :
    translate z j x = j (x + z) :=
  rfl

@[simp]
theorem translate_deriv (z : Vec d) (j : ShellField d) (x : Vec d) :
    deriv (translate z j) x = deriv j (x + z) :=
  rfl

@[simp]
theorem translate_secondDeriv (z : Vec d) (j : ShellField d) (x : Vec d) :
    secondDeriv (translate z j) x = secondDeriv j (x + z) :=
  rfl

theorem continuous_translate (z : Vec d) :
    Continuous (translate (d := d) z) :=
  Continuous.subtype_mk
    ((continuous_translateAmbient z).comp continuous_subtype_val)
    (fun j ↦ (translate z j).2)

theorem measurable_translate (z : Vec d) :
    Measurable (translate (d := d) z) :=
  (continuous_translate z).measurable

/-! ## Spatial scaling and triadic shell scaling -/

private def spatialMap (r : ℝ) : C(Vec d, Vec d) :=
  ⟨fun x ↦ r • x, continuous_id.const_smul r⟩

private def spatialSecondDerivativeMap (r : ℝ) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ]
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  (r • ContinuousLinearMap.id ℝ
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d)
      (Vec d →L[ℝ] Mat d)).flip
        (r • ContinuousLinearMap.id ℝ (Vec d)))

private def spatialSecondDerivativeContinuousMap (r : ℝ) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨spatialSecondDerivativeMap r, (spatialSecondDerivativeMap r).continuous⟩

private theorem spatialSecondDerivativeMap_eq_smul (r : ℝ)
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :
    spatialSecondDerivativeMap r H = r ^ 2 • H := by
  ext v w i k
  change r * H (r • v) w i k = r ^ 2 * H v w i k
  rw [H.map_smul]
  change r * (r * H v w i k) = r ^ 2 * H v w i k
  ring

private def spatialScaleAmbient (r : ℝ) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  (p.1.comp (spatialMap r),
    ((derivScaleMap r).comp (p.2.1.comp (spatialMap r)),
      (spatialSecondDerivativeContinuousMap r).comp
        (p.2.2.comp (spatialMap r))))

private theorem continuous_spatialScaleAmbient (r : ℝ) :
    Continuous (spatialScaleAmbient (d := d) r) :=
  ((ContinuousMap.continuous_precomp (spatialMap r)).comp continuous_fst).prodMk
    ((((ContinuousMap.continuous_postcomp (derivScaleMap r)).comp
      (ContinuousMap.continuous_precomp (spatialMap r))).comp
        continuous_snd.fst).prodMk
      (((ContinuousMap.continuous_postcomp
        (spatialSecondDerivativeContinuousMap r)).comp
          (ContinuousMap.continuous_precomp (spatialMap r))).comp
            continuous_snd.snd))

/-- Precompose with `x ↦ r • x`; the derivative carries the chain-rule
factor `r`. -/
def spatialScale (r : ℝ) (j : ShellField d) : ShellField d :=
  ⟨spatialScaleAmbient r j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simpa only [spatialScaleAmbient, spatialMap, derivScaleMap,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_comp,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
        Function.comp_def] using
        (j.hasFDerivAt (r • x)).comp x ((hasFDerivAt_id x).const_smul r)
    · intro x
      have hinner := (j.deriv_hasFDerivAt (r • x)).comp x
        ((hasFDerivAt_id x).const_smul r)
      have houter := hinner.const_smul r
      simpa only [spatialScaleAmbient, spatialMap, derivScaleMap,
        spatialSecondDerivativeContinuousMap, spatialSecondDerivativeMap,
        ContinuousMap.comp_apply, Function.comp_def] using houter
    · intro x i k
      simpa only [spatialScaleAmbient, spatialMap, ContinuousMap.comp_apply] using
        j.skew_entry (r • x) i k⟩

@[simp]
theorem spatialScale_apply (r : ℝ) (j : ShellField d) (x : Vec d) :
    spatialScale r j x = j (r • x) :=
  rfl

@[simp]
theorem spatialScale_deriv (r : ℝ) (j : ShellField d) (x : Vec d) :
    deriv (spatialScale r j) x = r • deriv j (r • x) :=
  rfl

@[simp]
theorem spatialScale_secondDeriv (r : ℝ) (j : ShellField d) (x : Vec d) :
    secondDeriv (spatialScale r j) x =
      r ^ 2 • secondDeriv j (r • x) :=
  spatialSecondDerivativeMap_eq_smul r (secondDeriv j (r • x))

theorem continuous_spatialScale (r : ℝ) :
    Continuous (spatialScale (d := d) r) :=
  Continuous.subtype_mk
    ((continuous_spatialScaleAmbient r).comp continuous_subtype_val)
    (fun j ↦ (spatialScale r j).2)

theorem measurable_spatialScale (r : ℝ) :
    Measurable (spatialScale (d := d) r) :=
  (continuous_spatialScale r).measurable

/-- Combined amplitude and spatial scaling. -/
def rescale (c r : ℝ) (j : ShellField d) : ShellField d :=
  scale c (spatialScale r j)

theorem continuous_rescale (c r : ℝ) :
    Continuous (rescale (d := d) c r) :=
  (continuous_scale c).comp (continuous_spatialScale r)

/-- The literal marginal scaling action `3^(γ k) j(3^(-k) ·)`. -/
def triadicScale (gamma : ℝ) (k : ℤ) (j : ShellField d) : ShellField d :=
  rescale (Real.rpow 3 (gamma * (k : ℝ))) (((3 : ℝ) ^ k)⁻¹) j

@[simp]
theorem triadicScale_apply (gamma : ℝ) (k : ℤ) (j : ShellField d)
    (x : Vec d) :
    triadicScale gamma k j x =
      Real.rpow 3 (gamma * (k : ℝ)) • j ((((3 : ℝ) ^ k)⁻¹) • x) :=
  rfl

theorem continuous_triadicScale (gamma : ℝ) (k : ℤ) :
    Continuous (triadicScale (d := d) gamma k) :=
  continuous_rescale _ _

theorem measurable_triadicScale (gamma : ℝ) (k : ℤ) :
    Measurable (triadicScale (d := d) gamma k) :=
  (continuous_triadicScale gamma k).measurable

/-! ## Negation -/

/-- Value and derivative negation, as required by J3. -/
def negate (j : ShellField d) : ShellField d :=
  scale (-1) j

@[simp]
theorem negate_apply (j : ShellField d) (x : Vec d) :
    negate j x = -j x := by
  simp only [negate, scale_apply, neg_one_smul]

@[simp]
theorem negate_deriv (j : ShellField d) (x : Vec d) :
    deriv (negate j) x = -deriv j x := by
  apply ContinuousLinearMap.ext
  intro v
  ext i k
  change (-1 : ℝ) * deriv j x v i k = -deriv j x v i k
  ring

@[simp]
theorem negate_secondDeriv (j : ShellField d) (x : Vec d) :
    secondDeriv (negate j) x = -secondDeriv j x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  ext i k
  change (-1 : ℝ) * secondDeriv j x v w i k =
    -secondDeriv j x v w i k
  ring

theorem continuous_negate : Continuous (negate (d := d)) :=
  continuous_scale (-1)

theorem measurable_negate : Measurable (negate (d := d)) :=
  continuous_negate.measurable

/-! ## Signed-permutation conjugation -/

private def matVecContinuousLinearMap (R : Mat d) : Vec d →L[ℝ] Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩

@[simp]
private theorem matVecContinuousLinearMap_apply (R : Mat d) (x : Vec d) :
    matVecContinuousLinearMap R x = matVecMul R x :=
  rfl

private def conjugateLinearMap (R : Mat d) : Mat d →ₗ[ℝ] Mat d where
  toFun M := matTranspose R * M * R
  map_add' M N := by
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

private def conjugateContinuousLinearMap (R : Mat d) : Mat d →L[ℝ] Mat d :=
  ⟨conjugateLinearMap R,
    (conjugateLinearMap R).continuous_of_finiteDimensional⟩

@[simp]
private theorem conjugateContinuousLinearMap_apply (R M : Mat d) :
    conjugateContinuousLinearMap R M = matTranspose R * M * R :=
  rfl

/-- The exact derivative action `D ↦ (M ↦ RᵀMR) ∘ D ∘ (v ↦ Rv)`. -/
private def rotateDerivativeMap (R : Mat d) :
    (Vec d →L[ℝ] Mat d) →L[ℝ] (Vec d →L[ℝ] Mat d) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Mat d) (Mat d)
      (conjugateContinuousLinearMap R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d) (Mat d)).flip
      (matVecContinuousLinearMap R))

@[simp]
private theorem rotateDerivativeMap_apply (R : Mat d)
    (D : Vec d →L[ℝ] Mat d) (v : Vec d) :
    rotateDerivativeMap R D v =
      matTranspose R * D (matVecMul R v) * R :=
  rfl

/-- The exact Hessian action
`H ↦ (v ↦ w ↦ Rᵀ H (Rv) (Rw) R)`. -/
private def rotateSecondDerivativeMap (R : Mat d) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ]
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  (ContinuousLinearMap.compL ℝ (Vec d)
      (Vec d →L[ℝ] Mat d) (Vec d →L[ℝ] Mat d)
      (rotateDerivativeMap R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d)
      (Vec d →L[ℝ] Mat d)).flip
        (matVecContinuousLinearMap R))

private def rotateValueMap (R : Mat d) : C(Mat d, Mat d) :=
  ⟨conjugateContinuousLinearMap R, (conjugateContinuousLinearMap R).continuous⟩

private def rotateDomainMap (R : Mat d) : C(Vec d, Vec d) :=
  ⟨matVecContinuousLinearMap R, (matVecContinuousLinearMap R).continuous⟩

private def rotateDerivativeContinuousMap (R : Mat d) :
    C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d) :=
  ⟨rotateDerivativeMap R, (rotateDerivativeMap R).continuous⟩

private def rotateSecondDerivativeContinuousMap (R : Mat d) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨rotateSecondDerivativeMap R, (rotateSecondDerivativeMap R).continuous⟩

private def rotateAmbient (R : Mat d) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  ((rotateValueMap R).comp (p.1.comp (rotateDomainMap R)),
    ((rotateDerivativeContinuousMap R).comp
      (p.2.1.comp (rotateDomainMap R)),
      (rotateSecondDerivativeContinuousMap R).comp
        (p.2.2.comp (rotateDomainMap R))))

private theorem continuous_rotateAmbient (R : Mat d) :
    Continuous (rotateAmbient (d := d) R) :=
  ((ContinuousMap.continuous_postcomp (rotateValueMap R)).comp
      ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
        continuous_fst)).prodMk
    (((ContinuousMap.continuous_postcomp (rotateDerivativeContinuousMap R)).comp
      ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
        continuous_snd.fst)).prodMk
      ((ContinuousMap.continuous_postcomp
          (rotateSecondDerivativeContinuousMap R)).comp
        ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
          continuous_snd.snd)))

/-- The signed-permutation action `j(x) ↦ Rᵀ j(Rx) R`. -/
def rotate (R : Mat d) (_hR : IsSignedPermutationMatrix R)
    (j : ShellField d) : ShellField d :=
  ⟨rotateAmbient R j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      have hinner := (j.hasFDerivAt (matVecMul R x)).comp x
        (matVecContinuousLinearMap R).hasFDerivAt
      have houter :=
        (conjugateContinuousLinearMap R).hasFDerivAt.comp x hinner
      simpa only [rotateAmbient, rotateValueMap, rotateDomainMap,
        rotateDerivativeContinuousMap, ContinuousMap.comp_apply,
        conjugateContinuousLinearMap_apply,
        matVecContinuousLinearMap_apply, rotateDerivativeMap_apply] using houter
    · intro x
      have hinner := (j.deriv_hasFDerivAt (matVecMul R x)).comp x
        (matVecContinuousLinearMap R).hasFDerivAt
      have houter := (rotateDerivativeMap R).hasFDerivAt.comp x hinner
      simpa only [rotateAmbient, rotateDomainMap,
        rotateDerivativeContinuousMap, rotateSecondDerivativeContinuousMap,
        ContinuousMap.comp_apply, matVecContinuousLinearMap_apply,
        rotateSecondDerivativeMap] using houter
    · intro x i k
      have hskew : matTranspose (j (matVecMul R x)) =
          -j (matVecMul R x) :=
        j.skew (matVecMul R x)
      have hmatrix :
          matTranspose (matTranspose R * j (matVecMul R x) * R) =
            -(matTranspose R * j (matVecMul R x) * R) := by
        calc
          matTranspose (matTranspose R * j (matVecMul R x) * R) =
              matTranspose R * matTranspose (j (matVecMul R x)) * R := by
                simp only [matTranspose, Matrix.transpose_mul,
                  Matrix.transpose_transpose, Matrix.mul_assoc]
          _ = matTranspose R * (-j (matVecMul R x)) * R := by
                rw [hskew]
          _ = -(matTranspose R * j (matVecMul R x) * R) := by
                rw [Matrix.mul_neg, Matrix.neg_mul]
      exact congrFun (congrFun hmatrix k) i⟩

@[simp]
theorem rotate_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (j : ShellField d) (x : Vec d) :
    rotate R hR j x = matTranspose R * j (matVecMul R x) * R :=
  rfl

theorem continuous_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Continuous (rotate (d := d) R hR) :=
  Continuous.subtype_mk
    ((continuous_rotateAmbient R).comp continuous_subtype_val)
    (fun j ↦ (rotate R hR j).2)

theorem measurable_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotate (d := d) R hR) :=
  (continuous_rotate R hR).measurable

/-! ## Compatibility with CoarseGraining regular-field operations -/

theorem forgetShell_translate (z : Vec d) (j : ShellField d) :
    forgetShell (translate z j) = translateReg z (forgetShell j) := by
  apply RegCoeffField.ext
  intro x
  rfl

theorem forgetShell_triadicScale (gamma : ℝ) (k : ℤ)
    (j : ShellField d) :
    forgetShell (triadicScale gamma k j) =
      Algsuperdiff.Probability.triadicLayerScaleReg gamma k (forgetShell j) := by
  apply RegCoeffField.ext
  intro x
  rfl

end

end Algsuperdiff.Frozen.Assumptions.ShellField
