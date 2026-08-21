/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OffGridComposeAssembly
import Algsuperdiff.Section4.Support.FluxCorrectedRepresentative

/-!
# The shallow re-parameterization, and the development carrier

The lower layer (`fluxCorrectedNormalizedBlockResponseRepresentative`) already
separates the correction cube `Q` from the response cube `R`, so the fix is a
shallow re-parameterization.

Two definitions

* `fluxCorrectedMaxDescendantAtRoot` — the descendant maximum over the shells of
  an **arbitrary root cube**, with the correction cube and the comparator held
  fixed;
* `fluxCorrectedErrorFunctionalAtRoot` — the corresponding error functional,

together with the reduction

```
fluxCorrectedErrorFunctionalAtRoot M L k (originCube d k) (originCube d k) s
    (isotropicComparatorMatrix (Annealed.sigmaBar M k))
  = fluxCorrectedErrorFunctional M L k s
```

which holds by `rfl`: the generalized object is a conservative extension of the
proved one, matching it exactly at the matched index.

## Main results

* `isEllipticFieldOn_fluxCorrectedRegField` — pointwise ellipticity on the
  half-open realization of a cube.
* `ae_forall_homogenizationErrorOnCube_eq_fluxCorrectedErrorFunctionalAtRoot` —
  the representative identification, at every root, on one event.
* `ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot` — **the
  composed estimate in the development carriers.**

## References

* ABK26, `e.mathcalE.stability.applied`.
* Repo, `fluxCorrectedNormalizedBlockResponseRepresentative` and
  `fluxCorrectedErrorFunctional` in
  `Section4/Support/FluxCorrectedRepresentative.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open Homogenization Homogenization.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Pointwise ellipticity of the flux-corrected field on a cube -/

/-- Duplicate of `FluxCorrectedRepresentative`'s `private
symmPart_fluxCorrectedRegField`. -/
private theorem symmPart_fluxCorrected' (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    symmPart (fluxCorrectedRegField M L m Q omega x) = M.nu • (1 : Mat d) := by
  ext i j
  have hA := congrFun (congrFun
    (Cutoff.symmPart_coefficientCutoff M.nu L omega x) i) j
  have hC := fluxIncrementAverage_skew M L m Q omega i j
  simp only [symmPart, fluxCorrectedRegField_apply, fluxCorrectedField_apply,
    Matrix.sub_apply] at hA ⊢
  linarith only [hA, hC]

/-- The half-open realization sits inside the closure of the open one: it is
contained in the closed ball of the same centre and radius. -/
private theorem cubeSet_subset_closure_openCubeSet (R : TriadicCube d) :
    cubeSet R ⊆ closure (openCubeSet R) := by
  rw [← ball_cubeCenter_eq_openCubeSet, closure_ball _ (cubeRadius_pos R).ne']
  exact cubeSet_subset_closedBall R

/-- The half-open cube also sits inside the canonical enclosing origin cube of
`Cutoff.cubeOriginCoverScale`, on which the cutoff entry envelope is stated. -/
private theorem cubeSet_subset_originCover (R : TriadicCube d) :
    cubeSet R ⊆ openCubeSet (originCube d (Cutoff.cubeOriginCoverScale R)) :=
  (cubeSet_subset_closure_openCubeSet R).trans (Cutoff.closure_subset_originCover R)

/-- The entry envelope of `FluxCorrectedRepresentative`'s `private
abs_fluxCorrectedRegField_entry_le`, on the **half-open** cube: the printed
containment `x + □_n ⊆ □_{n+2}` is a half-open containment, so the openness
restriction of the proved private lemma is removed here. -/
private theorem abs_fluxCorrected_entry_le' (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) {x : Vec d}
    (hx : x ∈ cubeSet R) (i j : Fin d) :
    |fluxCorrectedRegField M L m Q omega x i j| ≤
      fluxCorrectedCubeEntryBound M L m Q R omega := by
  have h1 : |Cutoff.coefficientCutoff M.nu L omega x i j| ≤
      Cutoff.coefficientCutoffCubeEntryBound M L omega R :=
    Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le
      (Cutoff.cubeOriginCoverScale R) L omega (cubeSet_subset_originCover R hx) i j
  have h2 := abs_fluxIncrementAverage_le_absSum M L m Q omega i j
  calc
    |fluxCorrectedRegField M L m Q omega x i j| =
        |Cutoff.coefficientCutoff M.nu L omega x i j -
          fluxIncrementAverage M L m Q omega i j| := by
      rw [fluxCorrectedRegField_apply, fluxCorrectedField_apply, Matrix.sub_apply]
    _ ≤ |Cutoff.coefficientCutoff M.nu L omega x i j| +
          |fluxIncrementAverage M L m Q omega i j| := abs_sub _ _
    _ ≤ fluxCorrectedCubeEntryBound M L m Q R omega := add_le_add h1 h2

/-- Duplicate of `FluxCorrectedRepresentative`'s `private
isEllipticMatrix_fluxCorrectedRegField`, on the half-open cube. -/
private theorem isEllipticMatrix_fluxCorrected' (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) {x : Vec d}
    (hx : x ∈ cubeSet R) :
    IsEllipticMatrix M.nu (fluxCorrectedCubeEllipticityUpper M L m Q R omega)
      (fluxCorrectedRegField M L m Q omega x) :=
  Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
    (symmPart_fluxCorrected' M L m Q omega x)
    (fun i j => abs_fluxCorrected_entry_le' M L m Q R omega hx i j)

/-- **Pointwise ellipticity of the flux-corrected field on a triadic cube.**

The proved witness is an *almost everywhere* statement; the countable
subadditivity consumes CoarseGraining's `IsEllipticFieldOn`, which is pointwise
on the set.  Both clauses are available from the proved ingredients, on the
half-open realization. -/
theorem isEllipticFieldOn_fluxCorrectedRegField (M : ABKModel d) (L m : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    IsEllipticFieldOn M.nu (fluxCorrectedCubeEllipticityUpper M L m Q R omega)
      (cubeSet R) (fluxCorrectedRegField M L m Q omega).toFun := by
  classical
  refine ⟨?_, fun x hx => isEllipticMatrix_fluxCorrected' M L m Q R omega hx⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact ((fluxCorrectedRegField M L m Q omega).entry_measurable i j).ite
    (measurableSet_cubeSet R) measurable_const

/-! ## 2. `F1'`: the shell root separated from the correction and comparator -/

/-- **The `F1'` descendant maximum.**  The shells are taken over the descendants of an
arbitrary `root` cube, while the flux correction (`Q`, at scale `m`) and the
comparator `a0` stay at the parent's index.  Compare
`fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative`, which forces
`root = Q`. -/
def fluxCorrectedMaxDescendantAtRoot [NeZero d] (M : ABKModel d) (L m : ℤ)
    (Q root : TriadicCube d) (k : ℤ) (a0 : Mat d) : Cutoff.CutoffSample d → ℝ :=
  fun omega => Ch02.finsetSupReal (descendantsAtScale root k)
    (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 omega)

theorem fluxCorrectedMaxDescendantAtRoot_nonneg [NeZero d] (M : ABKModel d) (L m : ℤ)
    (Q root : TriadicCube d) (k : ℤ) (a0 : Mat d) (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedMaxDescendantAtRoot M L m Q root k a0 omega := by
  refine Ch02.finsetSupReal_nonneg _ _ fun R _ => ?_
  exact fluxCorrectedNormalizedBlockResponseRepresentative_nonneg M L m Q R a0 omega

/-- Duplicate of `FluxCorrectedRepresentative`'s `private measurable_finset_sup'`. -/
private theorem measurable_finsetSup' {Omega iota : Type*} [MeasurableSpace Omega]
    {S : Finset iota} (hS : S.Nonempty) {f : iota → Omega → ℝ}
    (hf : ∀ i ∈ S, Measurable (f i)) :
    Measurable (S.sup' hS f) :=
  Finset.sup'_induction (s := S) (H := hS) (f := f)
    (p := fun g => Measurable g)
    (fun _ hf' _ hg' => hf'.sup hg')
    (fun i hi => hf i hi)

theorem measurable_fluxCorrectedMaxDescendantAtRoot [NeZero d] (M : ABKModel d) (L m : ℤ)
    (Q root : TriadicCube d) {k : ℤ} (hk : k ≤ root.scale) (a0 : Mat d) :
    Measurable (fluxCorrectedMaxDescendantAtRoot M L m Q root k a0) := by
  classical
  have hS : (descendantsAtScale root k).Nonempty := descendantsAtScale_nonempty root hk
  have hsup : Measurable
      ((descendantsAtScale root k).sup' hS
        (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0)) :=
    measurable_finsetSup' hS fun R _ =>
      measurable_fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0
  have hfun : fluxCorrectedMaxDescendantAtRoot M L m Q root k a0 =
      (descendantsAtScale root k).sup' hS
        (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0) := by
    funext omega
    rw [Finset.sup'_apply]
    exact Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' (descendantsAtScale root k) hS
      (fun R => fluxCorrectedNormalizedBlockResponseRepresentative M L m Q R a0 omega)
  rw [hfun]
  exact hsup

/-- **The `F1'` error functional.**  `𝓔_{s,∞,2}` at the cube `root`, taken with the
flux correction and the comparator of the *parent* index. -/
def fluxCorrectedErrorFunctionalAtRoot [NeZero d] (M : ABKModel d) (L m : ℤ)
    (Q root : TriadicCube d) (s : ℝ) (a0 : Mat d) : Cutoff.CutoffSample d → ℝ :=
  fun omega => Real.sqrt (∑' l : ℕ, Ch02.geometricWeight s 2 l *
    fluxCorrectedMaxDescendantAtRoot M L m Q root (root.scale - (l : ℤ)) a0 omega)

theorem fluxCorrectedErrorFunctionalAtRoot_nonneg [NeZero d] (M : ABKModel d) (L m : ℤ)
    (Q root : TriadicCube d) (s : ℝ) (a0 : Mat d) (omega : Cutoff.CutoffSample d) :
    0 ≤ fluxCorrectedErrorFunctionalAtRoot M L m Q root s a0 omega :=
  Real.sqrt_nonneg _

theorem measurable_fluxCorrectedErrorFunctionalAtRoot [NeZero d] (M : ABKModel d)
    (L m : ℤ) (Q root : TriadicCube d) {s : ℝ} (hs : 0 < s) (a0 : Mat d) :
    Measurable (fluxCorrectedErrorFunctionalAtRoot M L m Q root s a0) := by
  have hterm : ∀ l : ℕ, Measurable
      (fun omega => Ch02.geometricWeight s 2 l *
        fluxCorrectedMaxDescendantAtRoot M L m Q root (root.scale - (l : ℤ)) a0 omega) :=
    fun l => (measurable_fluxCorrectedMaxDescendantAtRoot M L m Q root
      (sub_le_self _ (by exact_mod_cast Nat.zero_le l)) a0).const_mul _
  exact Real.continuous_sqrt.measurable.comp
    (measurable_tsum_of_nonneg _ hterm (fun l omega => by
      refine mul_nonneg ?_ (fluxCorrectedMaxDescendantAtRoot_nonneg M L m Q root _ a0 omega)
      simpa only [Ch02.geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg l
          (mul_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 2))))

/-- **The `F1'` reduction.**  At the matched index the generalized functional is the
proved `fluxCorrectedErrorFunctional`, definitionally. -/
theorem fluxCorrectedErrorFunctionalAtRoot_eq [NeZero d] (M : ABKModel d) (L k : ℤ)
    (s : ℝ) :
    fluxCorrectedErrorFunctionalAtRoot M L k (originCube d k) (originCube d k) s
        (isotropicComparatorMatrix (Annealed.sigmaBar M k)) =
      fluxCorrectedErrorFunctional M L k s :=
  rfl

/-! ## 3. The representative identification, at every root -/

variable [NeZero d]

/-- On one probability-one event, CoarseGraining's `𝓔_{s,∞,2}` of the
flux-corrected family coincides with the `F1'` functional at **every** root cube. -/
theorem ae_forall_homogenizationErrorOnCube_eq_fluxCorrectedErrorFunctionalAtRoot
    (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ root : TriadicCube d,
      Ch02.HomogenizationErrorOnCube root s .infinity (.finite 2)
          (fluxCorrectedCoeffFamily M L m Q omega) a0 =
        fluxCorrectedErrorFunctionalAtRoot M L m Q root s a0 omega := by
  filter_upwards
    [ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative M L m Q a0]
    with omega hall
  intro root
  have hshell : ∀ l : ℕ,
      Ch02.maxDescendantNormalizedBlockResponseAtScale root (root.scale - (l : ℤ))
          (fluxCorrectedCoeffFamily M L m Q omega) a0 =
        fluxCorrectedMaxDescendantAtRoot M L m Q root (root.scale - (l : ℤ)) a0 omega := by
    intro l
    rw [Ch02.maxDescendantNormalizedBlockResponseAtScale, fluxCorrectedMaxDescendantAtRoot]
    exact congrArg (Ch02.finsetSupReal (descendantsAtScale root (root.scale - (l : ℤ))))
      (funext fun R => hall R)
  have hsq : (∑' l : ℕ, Ch02.geometricWeight s 2 l *
      fluxCorrectedMaxDescendantAtRoot M L m Q root (root.scale - (l : ℤ)) a0 omega) =
      Ch02.HomogenizationErrorOnCube root s .infinity (.finite 2)
        (fluxCorrectedCoeffFamily M L m Q omega) a0 ^ 2 := by
    rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum root hs _ a0]
    exact tsum_congr fun l => by rw [hshell l]
  rw [fluxCorrectedErrorFunctionalAtRoot, hsq]
  exact (Real.sqrt_sq (homogenizationErrorOnCube_infinity_two_nonneg root _ a0 hs)).symm

/-! ## 4. The composed estimate in the development carriers -/

/-- **The composed off-grid stability estimate in the development carriers.**

On one probability-one event, for every real translate `w`, every child cube
`P` and every lattice cube `K` with `w + □_P ⊆ □_K`:

```
𝓔_{t,∞,2}(w + □_P ; ã_{L,m}, σ̄_m)
    ≤ (36dt/((t−u)(1−2u)))^{1/2} · 3^{u(K.scale − P.scale)}
        · 𝓔_{u,∞,2}(□_K ; ã_{L,m}, σ̄_m) ,
```

Both printed depths (`K.scale − P.scale = 1, 2`) are instances. -/
theorem ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot
    (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d) (a0 : Mat d)
    {t u : ℝ} (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (w : Vec d) (P K : TriadicCube d),
        translateSet w (cubeSet P) ⊆ cubeSet K →
        offGridErrorFunctional w P t (fluxCorrectedRegField M L m Q omega).toFun a0 ≤
          Real.sqrt (offGridStabilityConst d t u) *
            ((3 : ℝ) ^ (u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
              fluxCorrectedErrorFunctionalAtRoot M L m Q K u a0 omega) := by
  filter_upwards
    [ae_forall_homogenizationErrorOnCube_eq_fluxCorrectedErrorFunctionalAtRoot
      M L m Q a0 hu0] with omega hall
  intro w P K hcontain
  have hg : ∀ S : TriadicCube d,
      ((fluxCorrectedCoeffFamily M L m Q omega).coeffOn S).toCoeffField =
        (fluxCorrectedRegField M L m Q omega).toFun := fun _ => rfl
  have hmeas : MeasurableSet (translateSet w (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub_const w)
  have hEll : IsEllipticFieldOn M.nu (fluxCorrectedCubeEllipticityUpper M L m Q K omega)
      (translateSet w (cubeSet P)) (fluxCorrectedRegField M L m Q omega).toFun :=
    IsEllipticFieldOn.mono (isEllipticFieldOn_fluxCorrectedRegField M L m Q K omega)
      hmeas hcontain
  have hmain := offGridErrorFunctional_le (w := w) (P := P) (K := K)
    (A := fluxCorrectedCoeffFamily M L m Q omega) (a0 := a0) hu0 hut ht hg hEll hcontain
  rw [← hall K]
  exact hmain

end

end Algsuperdiff.Section4.Provider.ExcessDecay
