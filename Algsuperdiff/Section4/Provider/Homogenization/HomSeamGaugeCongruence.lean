/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutSupport

/-!
# The multiscale clause's `∀ G` slot: the gauge is an a.e. functional

## What this file supplies

`HomSeamFluxIdentification.RecutCoreSupplyFluxEnergy`'s multiscale conjunct is
quantified over EVERY field `G` that agrees with `∇u − ∇v` on the open cube:

```text
  ∀ G, (∀ x ∈ □_m, G x = ∇u x − ∇v x) → CoarseGrainingFinitePMultiscale … G F.
```

The quantifier is FREE.  `CoarseGrainingFinitePMultiscale` reads its gradient
slot only through `negBesovLpPartialNorm`, which reads it only through the cell
averages `(G)_R` of the grid descendants `R ⊆ □_m`, and the cube average is an
a.e. functional of its integrand.  So the whole `∀ G` family collapses onto ONE
representative — the canonical `fun x => u.grad x - v.grad x`.

`coarseGrainingFinitePMultiscale_forall_of_eqOn` is that collapse, stated in
exactly the shape the supply's clause slot asks for.
-/

open Homogenization MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube average is an a.e. functional -/

/-- The scalar cube average sees its integrand only a.e. on the closed cube. -/
private theorem seamCubeAverage_congr_ae (R : TriadicCube d) {u v : Vec d → ℝ}
    (h : u =ᵐ[volume.restrict (cubeSet R)] v) :
    cubeAverage R u = cubeAverage R v := by
  unfold cubeAverage
  exact congrArg (fun t : ℝ => (cubeVolume R)⁻¹ * t) (integral_congr_ae h)

/-- The vector cube average sees its field only a.e. on the closed cube. -/
private theorem seamCubeAverageVec_congr_ae (R : TriadicCube d) {u v : Vec d → Vec d}
    (h : u =ᵐ[volume.restrict (cubeSet R)] v) :
    cubeAverageVec R u = cubeAverageVec R v := by
  funext i
  refine seamCubeAverage_congr_ae R ?_
  filter_upwards [h] with x hx
  exact congrFun hx i

/-- **THE CELL AVERAGE OF A DESCENDANT IS BLIND TO THE PARENT'S NULL SETS.**

If two fields agree pointwise on the OPEN parent cube, then every grid
descendant's cell average agrees.  This is the only way the finite-`p` gauge
touches its field. -/
theorem cubeAverageVec_congr_of_eqOn_openCube {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) {G G' : Vec d → Vec d}
    (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    cubeAverageVec R G = cubeAverageVec R G' :=
  seamCubeAverageVec_congr_ae R
    (ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR
      (ae_restrict_of_forall_mem (measurableSet_openCubeSet Q) hG))

/-! ## 2. The finite-`p` gauge, transported -/

/-- The depth-`j` `ℓ^p` mean is unchanged. -/
theorem negBesovLpDepthMean_congr_of_eqOn (Q : TriadicCube d) (p : ℝ) (j : ℕ)
    {G G' : Vec d → Vec d} (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    negBesovLpDepthMean Q p G j = negBesovLpDepthMean Q p G' j := by
  have hsum : (descendantsAverage Q j fun R =>
        Real.sqrt (vecNormSq (cubeAverageVec R G)) ^ p) =
      descendantsAverage Q j fun R =>
        Real.sqrt (vecNormSq (cubeAverageVec R G')) ^ p := by
    show ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, Real.sqrt (vecNormSq (cubeAverageVec R G)) ^ p =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, Real.sqrt (vecNormSq (cubeAverageVec R G')) ^ p
    refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [cubeAverageVec_congr_of_eqOn_openCube hR hG]
  rw [negBesovLpDepthMean_def, negBesovLpDepthMean_def, hsum]

/-- The weighted depth-`j` quantity is unchanged. -/
theorem negBesovLpDepthSeminorm_congr_of_eqOn (Q : TriadicCube d) (s p : ℝ) (j : ℕ)
    {G G' : Vec d → Vec d} (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    negBesovLpDepthSeminorm Q s p G j = negBesovLpDepthSeminorm Q s p G' j := by
  rw [negBesovLpDepthSeminorm_def, negBesovLpDepthSeminorm_def,
    negBesovLpDepthMean_congr_of_eqOn Q p j hG]

/-- **THE PARTIAL GAUGE IS BLIND TO THE REPRESENTATIVE.** -/
theorem negBesovLpPartialNorm_congr_of_eqOn (Q : TriadicCube d) (s p : ℝ) (N : ℕ)
    {G G' : Vec d → Vec d} (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    negBesovLpPartialNorm Q s p N G = negBesovLpPartialNorm Q s p N G' := by
  rw [negBesovLpPartialNorm_def, negBesovLpPartialNorm_def]
  refine congrArg (fun t : ℝ => t ^ (1 / p)) ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [negBesovLpDepthSeminorm_congr_of_eqOn Q s p j hG]

/-! ## 3. THE `∀ G` COLLAPSE -/

/-- **The multiscale clause transports along any representative.** -/
theorem CoarseGrainingFinitePMultiscale.congr_grad_of_eqOn {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {G G' Fflux : Vec d → Vec d}
    (h : CoarseGrainingFinitePMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen G Fflux)
    (hG : ∀ x ∈ openCubeSet Q, G x = G' x) :
    CoarseGrainingFinitePMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen G' Fflux := by
  intro S hS N
  have hkey := h S hS N
  rwa [negBesovLpPartialNorm_congr_of_eqOn Q s p N hG] at hkey

/-- **THE `∀ G` SLOT, PRODUCED FROM ONE REPRESENTATIVE.**

Exactly the shape `RecutCoreSupplyFluxEnergy`'s multiscale conjunct asks for:
the clause at the canonical difference field yields the clause at EVERY field
that agrees with it on the open cube, at no cost. -/
theorem coarseGrainingFinitePMultiscale_forall_of_eqOn {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {G0 Fflux : Vec d → Vec d}
    (h : CoarseGrainingFinitePMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen G0 Fflux) :
    ∀ G : Vec d → Vec d, (∀ x ∈ openCubeSet Q, G x = G0 x) →
      CoarseGrainingFinitePMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen G Fflux :=
  fun _ hG => h.congr_grad_of_eqOn fun x hx => (hG x hx).symm

end

end Algsuperdiff.Section4.Provider.Homogenization
