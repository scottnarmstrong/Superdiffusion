/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorDatum
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import Homogenization.Sobolev.PotentialSolenoidalL2

/-!
# The boundary regime of the coarse-grained Caccioppoli inequality with

`l.coarse.grained.Caccioppoli.RHS` is stated *with* a boundary datum `h`, and its
right-hand side carries the extra leg `t^{-3} Λ_t ‖∇h‖²_{H̲^{2t}(□_0)}`.  This
module proves the other half of the printed lemma's own proof, the **boundary
reduction**:

> let `v` be the Dirichlet solution on the whole cube with the same force `g`
> and the same boundary datum `h`; then `u - v` has zero trace on all of `∂□_0`
> and solves the *homogeneous* equation, so the zero-data theorem applies to it,
> and the `∇h`-leg is produced separately by the global energy estimate for `∇v`.

Landed here: everything about `u - v`.

## Main results

* This is what makes the boundary application legitimate at a patch that meets
  `∂□_m`.
* `memVectorL2_flux`, `isForcedEquation_sub` — the flux pairing is integrable
  and the difference of two forced solutions with the same force solves the
  homogeneous equation.
* `boundaryForcedCaccioppoliDatumOfDifference` — CoarseGraining's datum,
  populated for `u - v` at zero force.
* `exists_boundaryCaccioppoliEnergy_ofDifference` — CoarseGraining's coarse
  Caccioppoli applied to it: the core energy of `u - v` is bounded by the
  *pure* `L̲²` term, the force leg having vanished.

## What is not done here

Three things separate this from the printed boundary display on `x + □_n`:

1. the triangle inequality `‖σ^{1/2}∇u‖ ≤ ‖σ^{1/2}∇(u-v)‖ + ‖σ^{1/2}∇v‖` on the
   core (a quadratic-form Minkowski step);
2. the volume-ratio conversion of the *global* energy norm of `v` to the core
   (a `d`-only constant, needing a lower bound on `|caccioppoliCoreSet Q x|`);

None of the three is asserted anywhere in this file.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`, (the reduction), and its boundary
  application.
* CoarseGraining, `CoarseCaccioppoli/Theory.lean`, `Energy/Theory.lean`,
  `PublicInternalBridges/CoeffField.lean`,
  `Sobolev/PotentialSolenoidalL2.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. A global zero trace gives every localized zero trace -/

/-- **The boundary regime's trace discharge.**

If `u` has a *global* zero trace on `Ω` (i.e. `u ∈ H¹₀(Ω)`), then it satisfies
the localized zero-trace condition through an arbitrary window `V` — including
windows that meet `∂Ω`.  The multiplier need not be supported in `Ω`:
CoarseGraining's `H10Function.mulContDiffHasCompactSupport` multiplies the
*approximants*, whose supports already lie in `Ω`.

Together they cover both regimes of the anchor. -/
theorem localizedZeroTraceFunctionOn_of_memH10 {U V : Set (Vec d)} {u : Vec d → ℝ}
    (hu : MemH10 U u) : LocalizedZeroTraceFunctionOn U V u := by
  obtain ⟨w, hw⟩ := hu
  intro eta heta heta_compact _heta_sub
  refine ⟨w.mulContDiffHasCompactSupport heta heta_compact, ?_⟩
  rw [H10Function.mulContDiffHasCompactSupport_toFun]
  funext y
  show eta y * w.toH1Function.toFun y = eta y * u y
  rw [hw]

/-! ## 2. The flux pairing and the homogeneous difference equation -/

/-- The flux `a ∇u` of an `H¹` function is square integrable on the cube: the
coefficient field has an everywhere-elliptic representative (CoarseGraining's
`publicCoeffField`) agreeing with it almost everywhere. -/
theorem memVectorL2_flux (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
  have hB : MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul (publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn Q a) u.grad_memVectorL2
  refine hB.ae_eq ?_
  filter_upwards [publicCoeffField_ae_eq Q a] with x hx
  rw [hx]

/-- The matrix action is additive in the vector slot. -/
private theorem matVecMul_sub_right (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]

/-- The tested flux pairing is integrable. -/
theorem integrableOn_flux_pairing (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (φ : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    IntegrableOn
      (fun x => vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
        (φ.toH1Function.grad x))
      (Ch02.cubeDomain Q : Set (Vec d)) :=
  integrableOn_vecDot_of_memVectorL2 (memVectorL2_flux Q a u)
    φ.toH1Function.grad_memVectorL2

/-- **The difference of two forced solutions with the same force is a solution of
the homogeneous equation.**  This is the first step of the printed proof of
`l.coarse.grained.Caccioppoli.RHS`. -/
theorem isForcedEquation_sub {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    (hu : IsForcedEquation Q a u g) (hv : IsForcedEquation Q a v g) :
    IsForcedEquation Q a (u - v) (fun _ => 0) := by
  intro φ
  have hrw : ∀ x, vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u - v).grad x))
      (φ.toH1Function.grad x) =
      vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (φ.toH1Function.grad x) -
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
          (φ.toH1Function.grad x) := by
    intro x
    rw [H1Function.sub_grad]
    show vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x - v.grad x)) _ = _
    rw [matVecMul_sub_right]
    simp only [vecDot, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hzero : ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
      vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) ∂volume = 0 := by
    have : ∀ x : Vec d, vecDot ((0 : Vec d)) (φ.toH1Function.grad x) = 0 := by
      intro x
      simp [vecDot]
    simp only [this]
    exact integral_zero _ _
  rw [hzero]
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u - v).grad x))
          (φ.toH1Function.grad x) ∂volume
        = ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
            (vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
                (φ.toH1Function.grad x) -
              vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
                (φ.toH1Function.grad x)) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hrw x)
    _ = (∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
            vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
              (φ.toH1Function.grad x) ∂volume) -
          ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
            vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
              (φ.toH1Function.grad x) ∂volume :=
          integral_sub (integrableOn_flux_pairing Q a u φ)
            (integrableOn_flux_pairing Q a v φ)
    _ = 0 := by rw [hu φ, hv φ, sub_self]

/-! ## 3. The zero force is admissible -/

/-- The zero force has the `H^s` regularity CoarseGraining's Caccioppoli theorem
asks of its right-hand side. -/
theorem forceBesovRegularity_zero (Q : TriadicCube d) (s : ℝ) :
    ForceBesovRegularity Q s (fun _ : Vec d => (0 : Vec d)) where
  memLp := by
    have h : MemLp (0 : Vec d → Vec d) 2 (normalizedCubeMeasure Q) := MemLp.zero
    exact h
  partialSeminorms_bddAbove := by
    have h := cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove Q s
    exact h

/-! ## 4. The datum and the estimate -/

/-- **CoarseGraining's boundary Caccioppoli datum, populated by the difference of
two solutions with the same force and the same boundary datum.**

The localized zero trace is discharged *globally* (`u - v ∈ H¹₀`), so the patch
`x + □_{scale-1}` is arbitrary: it may meet `∂Q`.  That is precisely the
boundary regime the frozen theorem's general clause has to cover. -/
def boundaryForcedCaccioppoliDatumOfDifference {Q : TriadicCube d}
    {a : CoeffFamily d} (x : Vec d) {g : Vec d → Vec d}
    {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    (hu : IsForcedEquation Q a u g) (hv : IsForcedEquation Q a v g)
    (hdiff : MemH10 (Ch02.cubeDomain Q : Set (Vec d))
      (fun y => u.toFun y - v.toFun y)) :
    BoundaryForcedCaccioppoliDatum Q a x (fun _ => 0) where
  toH1 := u - v
  weakSolution := isForcedEquation_sub hu hv
  zeroTraceOnBoundaryPatch := by
    refine localizedZeroTraceFunctionOn_of_memH10 ?_
    have hfun : (u - v).toFun = fun y => u.toFun y - v.toFun y :=
      H1Function.sub_toFun u v
    rw [hfun]
    exact hdiff

/-- **The boundary-regime coarse Caccioppoli estimate for the difference.**

With the force gone, the right-hand side of CoarseGraining's theorem is the
pure `L̲²` term: the core energy of `u - v` is controlled by `λ_t 3^{-2·scale}`
times the `L̲²(Q)` mass of `u - v`, at the printed prefactor `(C/σ)^{2+4s/σ}
s^{-2s/σ} Θ_{s,t}^{(1-t)/σ}`.

This is the display `e.cgC.boundary.applied` of the printed proof. -/
theorem exists_boundaryCaccioppoliEnergy_ofDifference (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        {g : Vec d → Vec d}
        (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))),
        IsForcedEquation Q a u g → IsForcedEquation Q a v g →
        MemH10 (Ch02.cubeDomain Q : Set (Vec d))
          (fun y => u.toFun y - v.toFun y) →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        x ∈ openCubeSet Q →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) (u - v) ≤
            caccioppoliWithRHSPrefactor C Q a s t *
              (Ch02.lambdaS Q t a *
                Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y => u.toFun y - v.toFun y)) := by
  obtain ⟨C, hCpos, hC⟩ := (coarseCaccioppoliRHSTheory (d := d)).exists_constant
  refine ⟨C, hCpos, ?_⟩
  intro Q a s t x g u v hu hv hdiff hs hs1 ht ht2 hst hx
  have hbound := hC (boundaryForcedCaccioppoliDatumOfDifference x hu hv hdiff)
    hs hs1 ht ht2 hst hx (forceBesovRegularity_zero Q (2 * t))
  rw [boundaryForcedCaccioppoliCoreEnergy] at hbound
  rw [boundaryCaccioppoliWithRHSRHS, boundaryForcedCaccioppoliParentL2Sq] at hbound
  have hgradeq :
      (boundaryForcedCaccioppoliDatumOfDifference x hu hv hdiff).toH1.grad =
        (u - v).grad := rfl
  have hfuneq :
      (boundaryForcedCaccioppoliDatumOfDifference x hu hv hdiff).toH1.toFun =
        fun y => u.toFun y - v.toFun y := H1Function.sub_toFun u v
  rw [hfuneq] at hbound
  refine le_trans (le_of_eq ?_) (le_trans hbound (le_of_eq ?_))
  · rw [localizedCoeffEnergyValue, localizedCoeffEnergyValue, hgradeq]
  · rw [scaleNormalizedPositiveBesovVectorSeminormTwo]
    have hzero : cubeBesovPositiveVectorSeminormTwo Q (2 * t)
        (fun _ : Vec d => (0 : Vec d)) = 0 := by
      have h := cubeBesovPositiveVectorSeminormTwo_zero Q (2 * t)
      exact h
    rw [hzero]
    ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
