import Mathlib

/-!
# Statement-level audit vocabulary for the `AnomalousRegularity` comparator

Verbatim copy of the vocabulary of `Audit/AnomalousRegularity/Challenge.lean`
(challenge lines 88--507), Mathlib-only; a mechanical copy, not hand-edited.
-/

namespace Algsuperdiff
namespace StatementAudit
namespace AnomalousRegularity
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-! ## 1. Euclidean vectors and matrices -/
abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
instance instMatMeasurableSpace (d : ℕ) : MeasurableSpace (Mat d) := by
  change MeasurableSpace (Fin d → Fin d → ℝ); infer_instance
def vecDot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i
def vecNormSq {d : ℕ} (x : Vec d) : ℝ := vecDot x x
def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d := fun i => ∑ j, A i j * x j
def matTranspose {d : ℕ} (A : Mat d) : Mat d := Matrix.transpose A
/-- Euclidean `L²` norm of a vector (the ambient norm of `Vec d` itself is the
supremum norm). -/
noncomputable def vecNorm {d : ℕ} (x : Vec d) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖
/-- Euclidean/`L²` operator norm of a square real matrix. -/
noncomputable def matrixOperatorNorm {d : ℕ} (A : Mat d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, R i j = if i = σ j then s j else 0
def basisVec {d : ℕ} (i : Fin d) : Vec d := Pi.single i (1 : ℝ)

/-! ## 2. Triadic cubes -/
structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ
noncomputable def cubeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ := (3 : ℝ) ^ Q.scale
def openCubeSet {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i, (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }
/-- The centered triadic cube descriptor at scale `3^m`. -/
def originCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }

/-! ## 3. Regular shell fields: continuous matrix fields with stored continuous
first and second derivatives, antisymmetric at every point.  The matrix entries
carry the elementwise supremum norm. -/
def ShellField (d : ℕ) :=
  { p :
      ContinuousMap (Vec d) (Mat d) ×
        (ContinuousMap (Vec d) (Vec d →L[ℝ] Mat d) ×
          ContinuousMap (Vec d) (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) //
    (∀ x, HasFDerivAt p.1 (p.2.1 x) x) ∧
      (∀ x, HasFDerivAt p.2.1 (p.2.2 x) x) ∧
      ∀ x i j, p.1 x i j = -p.1 x j i }

noncomputable instance shellFieldTopologicalSpace (d : ℕ) :
    TopologicalSpace (ShellField d) := by
  unfold ShellField; infer_instance
noncomputable instance shellFieldMeasurableSpace (d : ℕ) : MeasurableSpace (ShellField d) :=
  borel (ShellField d)
instance shellFieldBorelSpace (d : ℕ) : BorelSpace (ShellField d) := ⟨rfl⟩
namespace ShellField
variable {d : ℕ}
instance : CoeFun (ShellField d) (fun _ => Vec d → Mat d) := ⟨fun j => j.1.1⟩
def deriv (j : ShellField d) : ContinuousMap (Vec d) (Vec d →L[ℝ] Mat d) := j.1.2.1
def secondDeriv (j : ShellField d) : ContinuousMap (Vec d) (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  j.1.2.2
theorem hasFDerivAt (j : ShellField d) (x : Vec d) : HasFDerivAt j (deriv j x) x := j.2.1 x
theorem deriv_hasFDerivAt (j : ShellField d) (x : Vec d) : HasFDerivAt (deriv j) (secondDeriv j x) x
    := j.2.2.1 x
theorem skew_entry (j : ShellField d) (x : Vec d) (i k : Fin d) : j x i k = -j x k i :=
  j.2.2.2 x i k
end ShellField

/-! ## 4. Spatial rescaling of a shell field: precomposition with `x ↦ r • x`,
the one shell transformation the lower-infinite cutoff observable needs.  The
stored derivatives carry the exact chain-rule factors. -/
abbrev ShellAmbient (d : ℕ) := ContinuousMap (Vec d) (Mat d) × (ContinuousMap (Vec d) (Vec d →L[ℝ]
    Mat d) × ContinuousMap (Vec d) (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)))
namespace ShellField
variable {d : ℕ}
def derivScaleMap (c : ℝ) : ContinuousMap (Vec d →L[ℝ] Mat d) (Vec d →L[ℝ] Mat d) :=
  ⟨fun D => c • D, continuous_id.const_smul c⟩
def spatialMap (r : ℝ) : ContinuousMap (Vec d) (Vec d) :=
  ⟨fun x => r • x, continuous_id.const_smul r⟩
def spatialSecondDerivativeMap (r : ℝ) : (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ] (Vec d →L[ℝ] (Vec d
    →L[ℝ] Mat d)) :=
  (r • ContinuousLinearMap.id ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))).comp ((ContinuousLinearMap.compL
  ℝ (Vec d) (Vec d) (Vec d →L[ℝ] Mat d)).flip (r • ContinuousLinearMap.id ℝ (Vec d)))

def spatialSecondDerivativeContinuousMap (r : ℝ) : ContinuousMap (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨spatialSecondDerivativeMap r, (spatialSecondDerivativeMap r).continuous⟩
def spatialScaleAmbient (r : ℝ) :
    ShellAmbient d → ShellAmbient d := fun p =>
  (p.1.comp (spatialMap r), ((derivScaleMap r).comp (p.2.1.comp (spatialMap r)),
      (spatialSecondDerivativeContinuousMap r).comp
        (p.2.2.comp (spatialMap r))))

/-- Precompose with `x ↦ r • x`; the derivative carries the chain-rule factor `r`. -/
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

end ShellField

/-! ## 5. Shell sequences and their canonical laws -/
abbrev ShellSeq (d : ℕ) := ℤ → ShellField d
namespace ShellField
variable {d : ℕ}
theorem measurable_shellCoordinate (k : ℤ) : Measurable (fun F : ShellSeq d => F k) :=
  measurable_pi_apply k
noncomputable def shellMarginalLaw (P : ProbabilityMeasure (ShellSeq d)) (k : ℤ) :
    ProbabilityMeasure (ShellField d) := P.map (measurable_shellCoordinate k).aemeasurable
noncomputable def zeroShellLaw (P : ProbabilityMeasure (ShellSeq d)) : ProbabilityMeasure
    (ShellField d) := P.map (measurable_shellCoordinate 0).aemeasurable
end ShellField

/-! ## 6. Regular coefficient fields: the entrywise Borel-measurable, locally
integrable matrix fields, with the σ-algebra generated jointly by point
evaluations and by compactly supported bounded entry integrals. -/
structure RegCoeffField (d : ℕ) where
  toFun : Vec d → Mat d
  entry_measurable : ∀ i j, Measurable (fun x : Vec d => toFun x i j)
  entry_locInt : ∀ i j, LocallyIntegrable (fun x : Vec d => toFun x i j) volume
namespace RegCoeffField
variable {d : ℕ}
instance : CoeFun (RegCoeffField d) (fun _ => Vec d → Mat d) := ⟨toFun⟩
end RegCoeffField
structure IsProbeR {d : ℕ} (φ : Vec d → ℝ) : Prop where
  measurable : Measurable φ
  bounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C
  hasCompactSupport : HasCompactSupport φ

def entryTestR {d : ℕ} (i j : Fin d) (φ : Vec d → ℝ) (a : RegCoeffField d) : ℝ :=
  ∫ x, a x i j * φ x ∂volume
def pointwiseSigmaR (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.comap RegCoeffField.toFun MeasurableSpace.pi
def entryTestSigmaR (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}

/-- The canonical measurable structure: the join of the two σ-algebras. -/
instance instMeasurableSpaceRegCoeffField (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  pointwiseSigmaR d ⊔ entryTestSigmaR d
/-- The local carrier σ-algebra on an observation set `U`: generated by the
entry-test preimages using only probes supported in `U`. -/
def LocalSigmaR {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ ∧ Function.support φ ⊆ U ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}
theorem locallyIntegrable_translate {d : ℕ} {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (z : Vec d) :
    LocallyIntegrable (fun x => f (x + z)) volume := by
  have hmap : Measure.map (Homeomorph.addRight z) (volume : Measure (Vec d)) = volume := by
    simpa [Homeomorph.coe_addRight] using
      (measurePreserving_add_right (volume : Measure (Vec d)) z).map_eq
  have hmapInt : LocallyIntegrable f (Measure.map (Homeomorph.addRight z) volume) := by
    rw [hmap]; exact hf
  exact (locallyIntegrable_map_homeomorph (Homeomorph.addRight z)).mp hmapInt

def translateReg {d : ℕ} (z : Vec d) (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x => a (x + z)
  entry_measurable := fun i j => (a.entry_measurable i j).comp (measurable_id.add measurable_const)
  entry_locInt := fun i j => locallyIntegrable_translate (a.entry_locInt i j) z

def ShellField.forgetShell {d : ℕ} (j : ShellField d) : RegCoeffField d where
  toFun := j
  entry_measurable := fun i k => ((continuous_apply k).comp ((continuous_apply i).comp
    j.1.1.continuous)).measurable
  entry_locInt := fun i k => ((continuous_apply k).comp ((continuous_apply i).comp
    j.1.1.continuous)).locallyIntegrable

def lihLocalSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (ShellField d) :=
  MeasurableSpace.comap (ShellField.forgetShell (d := d)) (LocalSigmaR U)
/-- The zero-shell regular-field law: the pushforward of the sequence law along
evaluation at coordinate zero followed by the forgetful map. -/
noncomputable def zeroShellRegMeasure {d : ℕ}
    (P : ProbabilityMeasure (ShellSeq d)) : Measure (RegCoeffField d) :=
  Measure.map (fun F : ShellSeq d => ShellField.forgetShell (F 0)) P.toMeasure

/-! ## 7. The (J2) cube observable: the weighted `C²` norm
`‖j‖_{L^∞(cu_0)} + √d ‖∇j‖ + d ‖∇²j‖` on the open unit cube, with all sizes
measured in exact Euclidean induced norms. -/
section J2Observable
variable {d : ℕ}
abbrev MatrixDerivative (d : ℕ) := Vec d →L[ℝ] Mat d
abbrev MatrixSecondDerivative (d : ℕ) := Vec d →L[ℝ] MatrixDerivative d
abbrev EuclideanUnitVector (d : ℕ) := {v : Vec d // vecNorm v ≤ 1}
def matrixDerivativeNormValue (D : MatrixDerivative d) :
    Option (EuclideanUnitVector d) → ℝ
  | none => 0
  | some v => matrixOperatorNorm (D v.1)

def matrixDerivativeNorm (D : MatrixDerivative d) : ℝ :=
  sSup (Set.range (matrixDerivativeNormValue D))
def matrixSecondDerivativeNormValue (H : MatrixSecondDerivative d) :
    Option (EuclideanUnitVector d) → ℝ
  | none => 0
  | some u => matrixDerivativeNorm (H u.1)

def matrixSecondDerivativeNorm (H : MatrixSecondDerivative d) : ℝ :=
  sSup (Set.range (matrixSecondDerivativeNormValue H))
abbrev UnitOpenCubePoint (d : ℕ) := {x : Vec d // x ∈ openCubeSet (originCube d 0)}
def unitCubeValueAtIndex (j : ShellField d) :
    Option (UnitOpenCubePoint d) → ℝ
  | none => 0
  | some x => matrixOperatorNorm (j x.1)

def unitCubeDerivAtIndex (j : ShellField d) :
    Option (UnitOpenCubePoint d) → ℝ
  | none => 0
  | some x => matrixDerivativeNorm (ShellField.deriv j x.1)

def unitCubeSecondDerivAtIndex (j : ShellField d) :
    Option (UnitOpenCubePoint d) → ℝ
  | none => 0
  | some x => matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1)

/-- Exact Euclidean matrix-operator `L∞` norm of the shell values on the literal
open unit cube.  The defining range includes zero explicitly. -/
def unitCubeValueNorm (j : ShellField d) : ℝ := sSup (Set.range (unitCubeValueAtIndex j))
def unitCubeDerivNorm (j : ShellField d) : ℝ := sSup (Set.range (unitCubeDerivAtIndex j))
def unitCubeSecondDerivNorm (j : ShellField d) : ℝ :=
  sSup (Set.range (unitCubeSecondDerivAtIndex j))
/-- The literal weighted observable in the manuscript's (J2) tail bound. -/
def j2Observable (d : ℕ) (j : ShellField d) : ℝ :=
  unitCubeValueNorm j + Real.sqrt d * unitCubeDerivNorm j + (d : ℝ) * unitCubeSecondDerivNorm j
end J2Observable

/-! ## 8. The stationary potential corrector: the Hilbert-space realization of
`∇ Δ⁻¹ div` on the zero-shell regular-field law.  The potential space is the
closed span of the strong horizontal gradients for the real translation action. -/
section Corrector
variable {d : ℕ}
/-- The Euclidean Hilbert realization of `ℝ^d`. -/
abbrev HilbertVec (d : ℕ) := PiLp 2 (fun _ : Fin d => ℝ)
def originForcing (e : Vec d) (a : RegCoeffField d) : HilbertVec d :=
  WithLp.toLp 2 (matVecMul (a 0) e)
variable {μ : Measure (RegCoeffField d)}
noncomputable def koopman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ) (z : Vec d) :
    Lp E 2 μ →ₗᵢ[ℝ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (translateReg z) (hstat z)

noncomputable def vectorL2Coord (i : Fin d) : Lp (HilbertVec d) 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) i).compLpL 2 μ
/-- `F` is the full strong horizontal gradient of `φ`. -/
def HasHorizontalGradient (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) μ μ)
    (φ : Lp ℝ 2 μ) (F : Lp (HilbertVec d) 2 μ) : Prop := ∀ i : Fin d,
  HasDerivAt (fun t : ℝ => koopman hstat (t • (Pi.single i 1 : Vec d)) φ)
    (vectorL2Coord (μ := μ) i F) 0
end Corrector
/-- `c` is the (J4) non-degeneracy constant of the law `P`: every Euclidean unit
direction `e` has a stationary potential corrector `chi` — in the closed span of
the strong horizontal gradients, with `originForcing e + chi` orthogonal to every
horizontal gradient — of exact energy `c · log 3`.  Those two properties pin
`chi` to the orthogonal-projection corrector, so the existential is not a
weakening.  The proof-valued arguments are universally quantified; both are
consequences of the model fields, and by proof irrelevance the display does not
depend on which proofs are supplied. -/
def RealizesCstar (d : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (c : ℝ) : Prop :=
  ∀ (hstat : ∀ z : Vec d, MeasurePreserving (translateReg (d := d) z) (zeroShellRegMeasure P)
    (zeroShellRegMeasure P)) (e : Vec d), vecNorm e = 1 →
  ∀ hmem : MemLp (originForcing e) 2 (zeroShellRegMeasure P),
  ∃ chi : Lp (HilbertVec d) 2 (zeroShellRegMeasure P),
    chi ∈ closure {F | ∃ φ, HasHorizontalGradient (μ := zeroShellRegMeasure P) hstat φ F} ∧
    (∀ (φ : Lp ℝ 2 (zeroShellRegMeasure P)) (F : Lp (HilbertVec d) 2 (zeroShellRegMeasure P)),
        HasHorizontalGradient (μ := zeroShellRegMeasure P) hstat φ F →
        inner ℝ (hmem.toLp (originForcing e) + chi) F = 0) ∧
    ‖chi‖ ^ 2 = c * Real.log 3
/-! ## 9. The standing model -/
open ProbabilityTheory in
/-- The standing ABK model.  Fields `nu` through `gamma_le_quarter` are the
paper-wide parameters; `independent` and `marginal_scaling` are the shell-law
prefix; `integrable`/`mean_zero`/`stationary`/`range_dependence` are (J1);
`gaussian_tail` is (J2); `hyperoctahedral`/`negation` are (J3); and
`nondegenerate` is (J4). -/
structure Model (d : ℕ) where
  nu : ℝ
  nu_pos : 0 < nu
  gamma : ℝ
  P : ProbabilityMeasure (ShellSeq d)
  dimension : 2 ≤ d
  gamma_pos : 0 < gamma
  gamma_le_quarter : gamma ≤ (1 : ℝ) / 4
  independent : iIndepFun (fun k : ℤ => fun F : ShellSeq d => F k) P.toMeasure
  marginal_scaling : ∀ (k : ℤ) (T : ShellField d → ShellField d) (hT : Measurable T),
    (∀ (j : ShellField d) (x : Vec d),
        T j x = Real.rpow 3 (gamma * (k : ℝ)) • j ((((3 : ℝ) ^ k)⁻¹) • x)) →
    ShellField.shellMarginalLaw P k = (ShellField.zeroShellLaw P).map hT.aemeasurable
  integrable : ∀ x : Vec d,
    Integrable (fun F : ShellSeq d => F 0 x) P.toMeasure
  mean_zero : ∀ x : Vec d,
    ∫ F : ShellSeq d, F 0 x ∂P.toMeasure = 0
  stationary : ∀ (z : Vec d) (T : ShellField d → ShellField d), Measurable T →
    (∀ (j : ShellField d) (x : Vec d), T j x = j (x + z)) →
    Measure.map T (ShellField.zeroShellLaw P).toMeasure =
      (ShellField.zeroShellLaw P).toMeasure
  range_dependence : ∀ U V : Set (Vec d),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ vecNorm (x - y)) →
      Indep (lihLocalSigma U) (lihLocalSigma V)
        (ShellField.zeroShellLaw P).toMeasure
  gaussian_tail : ∀ t : ℝ, 1 ≤ t →
    P.toMeasure {F | t < j2Observable d (F 0)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2)))
  hyperoctahedral : ∀ (R : Mat d), IsSignedPermutationMatrix R →
    ∀ (T : ShellSeq d → ShellSeq d) (hT : Measurable T),
      (∀ (F : ShellSeq d) (k : ℤ) (x : Vec d),
          T F k x = matTranspose R * F k (matVecMul R x) * R) →
      P.map hT.aemeasurable = P
  negation : ∀ (T : ShellSeq d → ShellSeq d) (hT : Measurable T),
    (∀ (F : ShellSeq d) (k : ℤ) (x : Vec d), T F k x = -(F k x)) →
    P.map hT.aemeasurable = P
  nondegenerate : ∃ cstar : ℝ, 0 < cstar ∧ RealizesCstar d P cstar

/-! ## 10. The lower-infinite cutoff: the truncated stream coefficient
`a_L = ν·Id + ∑_{k ≤ L} j_k`, on the full-measure carrier of shell samples whose
descending local-control series have bounded partial sums. -/
section Cutoff
variable {d : ℕ}
/-- A nonnegative control of a shell on the origin-centered cube at scale `ell`:
the unit-cube value norm after the corresponding spatial rescaling. -/
def localCubeControl (ell : ℤ) (j : ShellField d) : ℝ :=
  unitCubeValueNorm (ShellField.spatialScale (cubeScaleFactor (originCube d ell)) j)
def lowerTailPartialSum (ell m : ℤ) (q : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑ r ∈ Finset.range q, localCubeControl ell (omega (m - r))
def LowerTailBounded (ell m : ℤ) (omega : ShellSeq d) : Prop :=
  ∃ C : ℕ, ∀ q : ℕ, lowerTailPartialSum ell m q omega ≤ C
/-- The deterministic lower-tail good condition: for every pair of integer scales,
the descending-shell control series has bounded partial sums. -/
def LowerTailGood (omega : ShellSeq d) : Prop := ∀ ell m : ℤ, LowerTailBounded ell m omega
end Cutoff
abbrev CutoffSample (d : ℕ) := {omega : ShellSeq d // LowerTailGood omega}
/-- The canonical shell law on the cutoff carrier: the comap of the sequence law
along the subtype inclusion.  (That it is a probability measure is a theorem of
the model, not part of the statement.) -/
noncomputable def cutoffSampleMeasure {d : ℕ}
    (P : ProbabilityMeasure (ShellSeq d)) : Measure (CutoffSample d) :=
  Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) P.toMeasure
def cutoffValue {d : ℕ} (m : ℤ) (omega : CutoffSample d) (x : Vec d) : Mat d :=
  fun i j => ∑' r : ℕ, omega.1 (m - (r : ℤ)) x i j
/-- The coefficient cutoff `a_m = ν·Id + k_m`, where `k_m = ∑_{n ≤ m} j_n` is
the lower-infinite stream cutoff. -/
def coefficientCutoff {d : ℕ} (nu : ℝ) (m : ℤ) (omega : CutoffSample d) :
    Vec d → Mat d := fun x => nu • (1 : Mat d) + cutoffValue m omega x

/-! ## 11. Weak `H¹` solutions and the Dirichlet problem -/
section PDE
variable {d : ℕ}
abbrev MemL2On (U : Set (Vec d)) (u : Vec d → ℝ) : Prop := MemLp u 2 (volume.restrict U)
def GradMemL2On (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)
def HasWeakPartialDerivOn (U : Set (Vec d)) (i : Fin d) (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, u x *
  (fderiv ℝ φ x) (basisVec i) ∂volume = -∫ x in U, gi x * φ x ∂volume
def HasWeakGradientOn (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)
/-- A function together with a chosen weak gradient, both `L²` on `U`. -/
structure H1Function (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

/-- An `H¹` function with the usual smooth compactly supported approximation. -/
structure H10Function (U : Set (Vec d)) extends H1Function U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx : Filter.Tendsto (fun n => eLpNorm (fun x => approx n x - toH1Function.toFun x) 2
    (volume.restrict U)) Filter.atTop (nhds 0)
  tendsto_approx_grad : ∀ i : Fin d, Filter.Tendsto (fun n => eLpNorm (fun x => (fderiv ℝ (approx n)
    x) (basisVec i) - toH1Function.grad x i) 2 (volume.restrict U)) Filter.atTop (nhds 0)

/-- The divergence-form weak equation `-∇ · a ∇u = ∇ · g` on `W`, tested
against `H¹₀(W)`, in the distributional convention `⟪∇·g, φ⟫ = -∫ g·∇φ`. -/
def IsDivFormWeakSolutionOn (a : Vec d → Mat d) (W : Set (Vec d)) (u : H1Function W) (g : Vec d →
    Vec d) : Prop := ∀ φ : H10Function W, ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
    (φ.toH1Function.grad x) ∂volume = -∫ x in W, vecDot (g x) (φ.toH1Function.grad x) ∂volume
/-- The zero-trace boundary condition `u = h` on `∂W`, in the `H¹` sense:
`u ∈ h + H¹₀(W)`, with explicit witness. -/
def HasZeroTraceDifferenceOn (W : Set (Vec d)) (u h : H1Function W) : Prop :=
  ∃ w : H10Function W, (∀ x, u.toFun x = h.toFun x + w.toH1Function.toFun x) ∧ ∀ x, u.grad x =
  h.grad x + w.toH1Function.grad x
/-- The Dirichlet problem `-∇ · a ∇u = ∇ · g` in `□`, `u = h` on `∂□`, on the
open realization of the triadic cube `Q`. -/
def IsDirichletSolutionOn (a : Vec d → Mat d) (Q : TriadicCube d) (u h : H1Function (openCubeSet Q))
    (g : Vec d → Vec d) : Prop :=
  HasZeroTraceDifferenceOn (openCubeSet Q) u h ∧ IsDivFormWeakSolutionOn a (openCubeSet Q) u g
/-- `[f]_{C^{0,α}(U)} ≤ K` in explicit bound-predicate form; `|·|` is the
ambient (supremum) norm of `Vec d`. -/
def HolderSeminormBoundOn {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (alpha K : ℝ) (f : Vec d → E) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ alpha
def slopeCLM (A : Vec d) : Vec d →L[ℝ] ℝ := ∑ i : Fin d, A i • ContinuousLinearMap.proj i
/-- `f` is differentiable on `W` with gradient field `G`. -/
def HasGradientOn (W : Set (Vec d)) (f : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  ∀ y ∈ W, HasFDerivWithinAt f (slopeCLM (G y)) W y
/-- `⨍_A`, the volume-normalized restriction of Lebesgue measure to `A`. -/
noncomputable def normalizedVolumeMeasureOn (A : Set (Vec d)) : Measure (Vec d) :=
  (volume A)⁻¹ • volume.restrict A
end PDE

end

end AnomalousRegularity
end StatementAudit
end Algsuperdiff
