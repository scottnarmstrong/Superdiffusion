/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderLapTransfer
import Algsuperdiff.Section4.Support.Dirichlet
import Homogenization.Sobolev.Foundations.PoincareMeanZero

/-!
# Weyl's lemma by mollification (Weyl, part 2)

The competitor of the Schauder gradient-Hölder estimate is produced as an `H1Function W`
satisfying the variational condition `Support.IsWeaklyHarmonicOn`.  This module
proves that **every CoarseGraining convex smoothing of such a function is
classically harmonic on the interior ball**:

* `isWeaklyHarmonicOn_test_of_contDiff` — instantiate the `H¹₀` quantifier at a
  smooth compactly supported test;
* `isWeaklyHarmonicOn_integral_mul_euclideanCoordLaplacian_eq_zero` — the
  distributional form `∫_U u · Δψ = 0`, obtained by moving the remaining
  derivative off the gradient, one coordinate at a time;
* `euclideanCoordLaplacian_convolution_indicator_eq_zero` — hence the mollified
  function has vanishing coordinate Laplacian wherever the reflected kernel
  support stays inside `U`;
* `contDiff_convexApproxSmoothH1`,
  `euclideanCoordLaplacian_convexApproxSmoothH1_eq_zero`,
  `harmonicOnNhd_convexApproxSmoothH1_of_weaklyHarmonic` — the same for
  CoarseGraining's concrete convex smoothing `H1Function.convexApproxSmoothH1`,
  transported across `toEuc` into Mathlib's `HarmonicOnNhd` **at the full
  radius `r`**.

## Why the radius is not lost

The mollifier kernel `scaledConvexApproxKernel ρ (ε r)` is supported in the
sup-metric ball `closedBall 0 (ε r)`, and the convex smoothing evaluates the
convolution at the contracted point `(1-ε) • y + ε • x₀`, within sup-distance
`(1-ε) r` of `x₀`.  The two contributions add to exactly `r`, so no inner/outer
radius pair is needed; and the Euclidean ball is contained in the sup ball, so
the `HarmonicOnNhd` conclusion holds on `Metric.ball (toEuc x₀) r`.
-/

-- ==== transplanted from Superdiff/Regularity/Harmonic/WeylWeakLaplacian.lean ====
open MeasureTheory
open Homogenization (Vec basisVec vecDot H1Function H10Function euclideanGradient
  euclideanCoordDeriv euclideanCoordSecondDeriv euclideanCoordLaplacian)

open Algsuperdiff.Section4.Support (IsWeaklyHarmonicOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- **Unpack weak harmonicity at a smooth compactly supported test function.**  The `H¹₀` quantifier
in `IsWeaklyHarmonicOn` is instantiated at `Homogenization.H10Function.ofContDiff φ`. -/
theorem isWeaklyHarmonicOn_test_of_contDiff {U : Set (Vec d)} (hUopen : IsOpen U)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x) ∂volume = 0 := by
  simpa [Homogenization.H10Function.ofContDiff, Homogenization.H1Function.ofContDiff,
    Homogenization.euclideanGradient, Homogenization.euclideanCoordDeriv] using
    hu (Homogenization.H10Function.ofContDiff hUopen hφ hφ_supp hφ_sub)

/-- **Weakly harmonic `H¹` functions annihilate compactly supported Laplacian tests.**

`∫_U u · Δψ = 0` for smooth `ψ` with compact support inside `U`.  This is the distributional
(`−Δu = 0`) reading of the variational condition, and it is the form consumed by the convolution
harmonicity argument.

Proof: for each coordinate `i`, the weak derivative identity of `u` applied to the test function
`∂ᵢψ` (still smooth, still compactly supported inside `U`) gives
`∫_U u ∂ᵢ∂ᵢψ = -∫_U (∂ᵢu) (∂ᵢψ)`; summing over `i` turns the right-hand side into
`-∫_U ∇u · ∇ψ`, which vanishes by weak harmonicity. -/
theorem isWeaklyHarmonicOn_integral_mul_euclideanCoordLaplacian_eq_zero {U : Set (Vec d)}
    (hUopen : IsOpen U) {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_sub : tsupport ψ ⊆ U) :
    ∫ x in U, u x * euclideanCoordLaplacian ψ x ∂volume = 0 := by
  classical
  have hgrad_zero :
      ∫ x in U, vecDot (u.grad x) (euclideanGradient ψ x) ∂volume = 0 :=
    isWeaklyHarmonicOn_test_of_contDiff hUopen hu hψ hψ_supp hψ_sub
  -- one integration by parts per coordinate, against the test `∂ᵢψ`
  have hcomp : ∀ i : Fin d,
      ∫ x in U, u x * euclideanCoordSecondDeriv i i ψ x ∂volume =
        -∫ x in U, u.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
    intro i
    have hDψ_sub : tsupport (euclideanCoordDeriv i ψ) ⊆ U :=
      (Homogenization.tsupport_euclideanCoordDeriv_subset_tsupport i ψ).trans hψ_sub
    simpa [Homogenization.euclideanCoordSecondDeriv, Homogenization.euclideanCoordDeriv] using
      u.hasWeakPartialDerivOn i (euclideanCoordDeriv i ψ)
        (Homogenization.contDiff_euclideanCoordDeriv hψ i)
        (Homogenization.hasCompactSupport_euclideanCoordDeriv hψ_supp i) hDψ_sub
  -- integrability of the two families of products
  have hleftInt : ∀ i : Fin d,
      Integrable (fun x : Vec d => u x * euclideanCoordSecondDeriv i i ψ x)
        (volume.restrict U) := by
    intro i
    have hsecond_mem :
        MemLp (euclideanCoordSecondDeriv i i ψ) 2 (volume.restrict U) :=
      (((Homogenization.contDiff_euclideanCoordSecondDeriv hψ i
            i).continuous).memLp_of_hasCompactSupport
        (Homogenization.hasCompactSupport_euclideanCoordSecondDeriv hψ_supp i i)).restrict U
    simpa [MeasureTheory.IntegrableOn] using u.memL2.integrable_mul hsecond_mem
  have hrightInt : ∀ i : Fin d,
      Integrable (fun x : Vec d => u.grad x i * euclideanCoordDeriv i ψ x)
        (volume.restrict U) := by
    intro i
    have hderiv_mem : MemLp (euclideanCoordDeriv i ψ) 2 (volume.restrict U) :=
      (((Homogenization.contDiff_euclideanCoordDeriv hψ i).continuous).memLp_of_hasCompactSupport
        (Homogenization.hasCompactSupport_euclideanCoordDeriv hψ_supp i)).restrict U
    simpa [MeasureTheory.IntegrableOn] using (u.grad_memL2 i).integrable_mul hderiv_mem
  calc
    ∫ x in U, u x * euclideanCoordLaplacian ψ x ∂volume
        = ∫ x in U, ∑ i : Fin d, u x * euclideanCoordSecondDeriv i i ψ x ∂volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          simp [Homogenization.euclideanCoordLaplacian, Finset.mul_sum]
    _ = ∑ i : Fin d, ∫ x in U, u x * euclideanCoordSecondDeriv i i ψ x ∂volume :=
          MeasureTheory.integral_finset_sum Finset.univ fun i _ => hleftInt i
    _ = ∑ i : Fin d, -∫ x in U, u.grad x i * euclideanCoordDeriv i ψ x ∂volume :=
          Finset.sum_congr rfl fun i _ => hcomp i
    _ = -∑ i : Fin d, ∫ x in U, u.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x in U, ∑ i : Fin d, u.grad x i * euclideanCoordDeriv i ψ x ∂volume := by
          rw [MeasureTheory.integral_finset_sum Finset.univ fun i _ => hrightInt i]
    _ = -∫ x in U, vecDot (u.grad x) (euclideanGradient ψ x) ∂volume := rfl
    _ = 0 := by rw [hgrad_zero, neg_zero]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== transplanted from Superdiff/Regularity/Harmonic/WeylMollification.lean ====
open scoped Convolution
open MeasureTheory InnerProductSpace
open Homogenization (Vec H1Function IsConvexApproxKernel IsOpenBoundedConvexDomain
  scaledConvexApproxKernel convexApproxSmoothRepresentative unitConvexApproxKernel
  unitConvexApproxScale euclideanCoordLaplacian)

open Algsuperdiff.Section4.Support (IsWeaklyHarmonicOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ### Support geometry of the scaled mollifier -/

/-- A scaled convex-approximation kernel is supported in the correspondingly scaled sup-metric
ball. -/
theorem tsupport_scaledConvexApproxKernel_subset_closedBall {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) {a : ℝ} (ha : 0 < a) :
    tsupport (scaledConvexApproxKernel ρ a) ⊆ Metric.closedBall (0 : Vec d) a := by
  have hsupport :
      Function.support (scaledConvexApproxKernel ρ a) ⊆ Metric.closedBall (0 : Vec d) a := by
    intro y hy
    have hyρ_nonzero : ρ (a⁻¹ • y) ≠ 0 := by
      intro hzero
      exact hy (by simp [Homogenization.scaledConvexApproxKernel, hzero])
    have hyρ : a⁻¹ • y ∈ tsupport ρ := subset_tsupport ρ hyρ_nonzero
    have hnorm : ‖a⁻¹ • y‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.support_subset_closedBall hyρ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hy_eq : y = a • (a⁻¹ • y) := by
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    calc ‖y - 0‖ = ‖y‖ := by simp
      _ = ‖a • (a⁻¹ • y)‖ := congrArg norm hy_eq
      _ = a * ‖a⁻¹ • y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left hnorm ha.le
      _ = a := by ring
  exact closure_minimal hsupport Metric.isClosed_closedBall

/-- **The reflected mollifier stays inside the ball.**  If `y` lies in the sup-metric closed ball
`Metric.closedBall x₀ r` and `0 < ε ≤ 1`, then the support of the reflected `ε r`-scaled kernel
around the contracted sample point `A = (1-ε) • y + ε • x₀` is contained in the *same* closed ball
`Metric.closedBall x₀ r`.

The two contributions add exactly: `dist z A ≤ ε r` (kernel support) and
`dist A x₀ = (1-ε) · dist y x₀ ≤ (1-ε) r` (contraction). -/
theorem tsupport_scaledConvexApproxKernel_reflect_subset_closedBall {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) {x₀ y : Vec d} {r ε : ℝ}
    (hy : y ∈ Metric.closedBall x₀ r) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    tsupport (fun z : Vec d =>
        scaledConvexApproxKernel ρ (ε * r) (((1 - ε) • y + ε • x₀) - z))
      ⊆ Metric.closedBall x₀ r := by
  intro z hz
  set A : Vec d := (1 - ε) • y + ε • x₀ with hA
  set K : Vec d → ℝ := scaledConvexApproxKernel ρ (ε * r) with hKdef
  have hεr_pos : 0 < ε * r := mul_pos hε0 hr
  have hzA_support : A - z ∈ tsupport K := by
    have hz' : z ∈ tsupport (K ∘ Homeomorph.subLeft A) := by
      simpa [K, A, Function.comp_def] using hz
    rwa [tsupport_comp_eq_preimage K (Homeomorph.subLeft A)] at hz'
  have hzA_closed : A - z ∈ Metric.closedBall (0 : Vec d) (ε * r) :=
    tsupport_scaledConvexApproxKernel_subset_closedBall hρ hεr_pos hzA_support
  have hdist_zA : dist z A ≤ ε * r := by
    have hswap : dist z A = dist (A - z) (0 : Vec d) := by
      simp [dist_eq_norm, norm_sub_rev]
    rw [hswap]
    simpa [Metric.mem_closedBall] using hzA_closed
  have hA_sub : A - x₀ = (1 - ε) • (y - x₀) := by
    funext i
    simp only [hA, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdist_Ax : dist A x₀ = (1 - ε) * dist y x₀ := by
    rw [dist_eq_norm, dist_eq_norm, hA_sub, norm_smul,
      Real.norm_of_nonneg (sub_nonneg.mpr hε1)]
  have hyx : dist y x₀ ≤ r := by simpa [Metric.mem_closedBall] using hy
  have hdist_Ax_le : dist A x₀ ≤ (1 - ε) * r := by
    rw [hdist_Ax]
    exact mul_le_mul_of_nonneg_left hyx (sub_nonneg.mpr hε1)
  rw [Metric.mem_closedBall]
  calc dist z x₀ ≤ dist z A + dist A x₀ := dist_triangle z A x₀
    _ ≤ ε * r + (1 - ε) * r := add_le_add hdist_zA hdist_Ax_le
    _ = r := by ring

/-! ### The convolution harmonicity core -/

/-- **The mollified weakly harmonic function has vanishing Laplacian.**  If the *reflected* kernel
`y ↦ K (A - y)` is supported inside `U` and `u` is weakly harmonic on `U`, then the coordinate
Laplacian of the convolution `K ⋆ (𝟙_U u)` vanishes at `A`.

Proof: the Laplacian passes onto the kernel (`euclideanCoordLaplacian_convolution_left`); a change
of variables (`integral_mul_indicator_const_sub_eq_setIntegral`) turns the resulting global integral
into the pairing `∫_U u · Δψ` with `ψ y = K (A - y)`; and the point reflection leaves the Laplacian
invariant (`euclideanCoordLaplacian_comp_const_sub`), so the pairing vanishes by
`IsWeaklyHarmonicOn.integral_mul_euclideanCoordLaplacian_eq_zero`. -/
theorem euclideanCoordLaplacian_convolution_indicator_eq_zero {U : Set (Vec d)}
    (hUopen : IsOpen U) {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {K : Vec d → ℝ} (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (A : Vec d)
    (hsub : tsupport (fun y : Vec d => K (A - y)) ⊆ U) :
    euclideanCoordLaplacian
        (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun) A = 0 := by
  have hUm : MeasurableSet U := hUopen.measurableSet
  have hmem_indicator : MemLp (Set.indicator U u.toFun) 2 volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hUm]
    exact u.memL2
  have hloc_indicator : LocallyIntegrable (Set.indicator U u.toFun) volume :=
    hmem_indicator.locallyIntegrable (by norm_num)
  set ψ : Vec d → ℝ := fun y => K (A - y) with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hK.comp (contDiff_const.sub contDiff_id)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (K ∘ Homeomorph.subLeft A)
    simpa [ψ, Function.comp_def] using hK_supp.comp_homeomorph (Homeomorph.subLeft A)
  have hweak_zero : ∫ y in U, u y * euclideanCoordLaplacian ψ y ∂volume = 0 :=
    isWeaklyHarmonicOn_integral_mul_euclideanCoordLaplacian_eq_zero hUopen hu hψ hψ_supp hsub
  have hweak_zero' : ∫ y in U, u y * euclideanCoordLaplacian K (A - y) ∂volume = 0 := by
    refine Eq.trans ?_ hweak_zero
    refine MeasureTheory.setIntegral_congr_fun hUm fun y _ => ?_
    congr 1
    exact (euclideanCoordLaplacian_comp_const_sub hK A y).symm
  rw [euclideanCoordLaplacian_convolution_left hK_supp hK hloc_indicator,
    MeasureTheory.convolution_def]
  simpa using
    (integral_mul_indicator_const_sub_eq_setIntegral hUm A (euclideanCoordLaplacian K)
      u.toFun).trans hweak_zero'

/-! ### The CoarseGraining convex smoothing is harmonic on the ball -/

/-- **The convex smoothing of a weakly harmonic function has vanishing Laplacian on the ball.**
This is the coordinate form of the mollified-harmonicity core: the smoothing operator is the
convolution `K_{εr} ⋆ (𝟙_U u)` read at the contracted point `(1-ε) • y + ε • x₀`,
so its Laplacian is
`(1-ε)²` times the convolution Laplacian there, which vanishes by
`euclideanCoordLaplacian_convolution_indicator_eq_zero` and the support geometry. -/
theorem euclideanCoordLaplacian_convexApproxSmoothRepresentative_eq_zero {U : Set (Vec d)}
    (hUopen : IsOpen U) {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) {x₀ : Vec d} {r ε : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {y : Vec d} (hy : y ∈ Metric.closedBall x₀ r) :
    euclideanCoordLaplacian (convexApproxSmoothRepresentative U ρ u.toFun x₀ r ε) y = 0 := by
  have hUm : MeasurableSet U := hUopen.measurableSet
  have hεr_pos : 0 < ε * r := mul_pos hε0 hr
  set K : Vec d → ℝ := scaledConvexApproxKernel ρ (ε * r) with hKdef
  have hK : ContDiff ℝ (⊤ : ℕ∞) K := Homogenization.contDiff_scaledConvexApproxKernel hρ _
  have hK_supp : HasCompactSupport K :=
    Homogenization.hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hεr_pos
  have hmem_indicator : MemLp (Set.indicator U u.toFun) 2 volume := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hUm]
    exact u.memL2
  have hloc_indicator : LocallyIntegrable (Set.indicator U u.toFun) volume :=
    hmem_indicator.locallyIntegrable (by norm_num)
  set F : Vec d → ℝ :=
    K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun with hFdef
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    HasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume) hK_supp hK hloc_indicator
  have hrepr : convexApproxSmoothRepresentative U ρ u.toFun x₀ r ε
      = fun x => F ((1 - ε) • x + ε • x₀) := rfl
  rw [hrepr, euclideanCoordLaplacian_comp_smul_add hF (1 - ε) (ε • x₀) y]
  have hzero : euclideanCoordLaplacian F ((1 - ε) • y + ε • x₀) = 0 :=
    euclideanCoordLaplacian_convolution_indicator_eq_zero hUopen hu hK_supp hK _
      ((tsupport_scaledConvexApproxKernel_reflect_subset_closedBall hρ hy hr hε0 hε1).trans hball)
  rw [hzero, mul_zero]

/-- The concrete CoarseGraining convex `H¹` smoothing has a globally `C^∞`
representative. -/
theorem contDiff_convexApproxSmoothH1 {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      ((Homogenization.H1Function.convexApproxSmoothH1 (U := U) hU u x₀ hr n : Vec d → ℝ)) := by
  rw [Homogenization.H1Function.convexApproxSmoothH1_toFun]
  exact Homogenization.contDiff_convexApproxSmoothRepresentative
    (U := U) (ρ := unitConvexApproxKernel (d := d)) (u := u.toFun) (p := (2 : ENNReal))
    (x0 := x₀) (r := r) (ε := unitConvexApproxScale n)
    hU.isOpen.measurableSet (Homogenization.isConvexApproxKernel_unitConvexApproxKernel (d := d))
    (by norm_num : (1 : ENNReal) ≤ 2) u.memL2 hr
    (by dsimp [Homogenization.unitConvexApproxScale]; positivity)

/-- **Vanishing Laplacian of the CoarseGraining convex smoothing**, on the whole
sup-metric ball. -/
theorem euclideanCoordLaplacian_convexApproxSmoothH1_eq_zero {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x₀ r ⊆ U) (n : ℕ)
    {y : Vec d} (hy : y ∈ Metric.closedBall x₀ r) :
    euclideanCoordLaplacian
      ((Homogenization.H1Function.convexApproxSmoothH1 (U := U) hU u x₀ hr n : Vec d → ℝ)) y
      = 0 := by
  rw [Homogenization.H1Function.convexApproxSmoothH1_toFun]
  refine euclideanCoordLaplacian_convexApproxSmoothRepresentative_eq_zero hU.isOpen hu
    (Homogenization.isConvexApproxKernel_unitConvexApproxKernel (d := d)) hr hball ?_ ?_ hy
  · dsimp [Homogenization.unitConvexApproxScale]; positivity
  · exact Homogenization.unitConvexApproxScale_le_one n

/-- **Mollified-harmonicity core, in mathlib vocabulary.**  For `u` weakly harmonic
on the open bounded convex domain `U` and `Metric.closedBall x₀ r ⊆ U`, every
CoarseGraining convex smoothing of `u` is a genuine
`InnerProductSpace.HarmonicOnNhd` function on the Euclidean ball `Metric.ball
(toEuc x₀) r` (after transport across the coordinate identification `toEuc`). -/
theorem harmonicOnNhd_convexApproxSmoothH1_of_weaklyHarmonic {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {u : H1Function U} (hu : IsWeaklyHarmonicOn U u)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x₀ r ⊆ U) (n : ℕ) :
    HarmonicOnNhd
      (((Homogenization.H1Function.convexApproxSmoothH1 (U := U) hU u x₀ hr n : Vec d → ℝ))
        ∘ toEuc.symm)
      (Metric.ball (toEuc x₀) r) := by
  have hcd : ContDiff ℝ 2
      ((Homogenization.H1Function.convexApproxSmoothH1 (U := U) hU u x₀ hr n : Vec d → ℝ)) :=
    (contDiff_convexApproxSmoothH1 hU u x₀ hr n).of_le (by norm_cast)
  refine harmonicOnNhd_ball_comp_toEuc_symm hcd hr fun y hy => ?_
  exact euclideanCoordLaplacian_convexApproxSmoothH1_eq_zero hU hu hr hball n
    (Metric.ball_subset_closedBall hy)

/-! ### The `L²` approximation apex -/

/-! ### `MemLp` bookkeeping for the smooth approximant on a bounded window -/

/-! ### The apex on a supplied measurable window -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

