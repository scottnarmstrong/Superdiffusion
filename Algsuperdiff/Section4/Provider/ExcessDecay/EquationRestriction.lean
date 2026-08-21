/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry
import Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestrictionZeroExtension
import Algsuperdiff.Section4.Support.Dirichlet

/-!
# Restricting the anchor's equation to the parent window

This module performs the restriction.

CoarseGraining proves exactly this for *triadic descendants*
(`Ch03.ABK26.IsForcedEquation.restrictToDescendant`) by zero-extending the
descendant test function; the window `z + □_{n+2}` is a translate by an
arbitrary real `z` and is not a triadic cube, so the descendant version does
not apply.  The general statement — restriction to an **arbitrary open subset**
— is proved here by the same two-line mechanism at `h10ExtendToSuperset`
(`EquationRestrictionZeroExtension.lean`: the `p = 2` re-derivation of
CoarseGraining's unavailable `H10Function.extendByZeroToOpenSuperset`) and
`H1Function.restrict`.

## Sign conventions

`Support.IsDivFormWeakSolutionOn` renders `-∇·a∇u = ∇·g` with the minus sign on
the right (`⟪∇·g, φ⟫ = -∫ g·∇φ`); CoarseGraining's `Ch03.IsForcedEquation`
fixes the opposite convention.  The bridge below is therefore stated at the
**negated** forcing, exactly as `Support/Dirichlet.lean` documents for
CoarseGraining's `IsZeroTraceDirichletRhsWeakSolution`.  Every right-hand side
of the frozen theorem is a seminorm of `g`, invariant under `g ↦ -g`.

## Main results

* `isDivFormWeakSolutionOn_restrict` — the weak equation restricts to every open
  subset.
* `isDivFormWeakSolutionOn_translateWindow_of_frontier_inter_empty` — the same at
  the anchor's own gate and window `z + □_k ⊆ □_m`.
* `isForcedEquation_of_isDivFormWeakSolutionOn` (and the converse) — the
  convention bridge to CoarseGraining's cube predicate.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
* CoarseGraining, `Homogenization/Book/Ch03/ABK26/LocalCoarseGraining.lean`
  (`IsForcedEquation.restrictToDescendant`),
  `Homogenization/Sobolev/H1/BasicLemmas.lean` (`H1Function.restrict`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The zero-extension identity for set integrals -/

/-- Pairing a field against the gradient of a zero-extended `H¹₀` test on the
larger set is pairing it against the original gradient on the smaller set.
Disclosed re-derivation of an CoarseGraining private; see the module docstring. -/
private theorem setIntegral_vecDot_extendByZero {V W : Set (Vec d)}
    (hV : MeasurableSet V) (hVW : V ⊆ W) (F : Vec d → Vec d)
    (phi : H10Function V) :
    ∫ x in W, vecDot (F x)
        ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x) ∂volume =
      ∫ x in V, vecDot (F x) (phi.toH1Function.grad x) ∂volume := by
  have hindicator :
      (fun x => vecDot (F x)
          ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x)) =
        V.indicator (fun x => vecDot (F x) (phi.toH1Function.grad x)) := by
    funext x
    rw [h10ExtendToSuperset_grad phi hV hVW]
    by_cases hx : x ∈ V
    · simp only [h10ZeroExtensionGrad_of_mem phi hx, Set.indicator_of_mem hx]
    · simp only [h10ZeroExtensionGrad_of_not_mem phi hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  rw [hindicator, MeasureTheory.integral_indicator hV,
    Measure.restrict_restrict hV, Set.inter_eq_left.mpr hVW]

/-! ## 2. The restriction to an arbitrary open subset -/

/-- **The divergence-form weak equation restricts to every open subset.**

If `-∇·a∇u = ∇·g` weakly on `W` and `V ⊆ W` is open, then the same equation
holds weakly on `V` for the restriction of `u`.  The arbitrary-open-subset
generalization of `Ch03.ABK26.IsForcedEquation.restrictToDescendant`. -/
theorem isDivFormWeakSolutionOn_restrict {W V : Set (Vec d)}
    (hV : IsOpen V) (hVW : V ⊆ W) {a : CoeffField d} {u : H1Function W}
    {g : Vec d → Vec d} (h : Support.IsDivFormWeakSolutionOn a W u g) :
    Support.IsDivFormWeakSolutionOn a V (u.restrict hV hVW) g := by
  intro phi
  have hflux := setIntegral_vecDot_extendByZero hV.measurableSet hVW
    (fun x => matVecMul (a x) (u.grad x)) phi
  have hforcing := setIntegral_vecDot_extendByZero hV.measurableSet hVW g phi
  have hgradEq : (u.restrict hV hVW).grad = u.grad := rfl
  calc
    ∫ x in V, vecDot (matVecMul (a x) ((u.restrict hV hVW).grad x))
          (phi.toH1Function.grad x) ∂volume =
        ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
          ((h10ExtendToSuperset phi hV.measurableSet hVW).toH1Function.grad x)
          ∂volume := by
          rw [hgradEq, hflux]
    _ = -∫ x in W, vecDot (g x)
          ((h10ExtendToSuperset phi hV.measurableSet hVW).toH1Function.grad x)
          ∂volume :=
      h (h10ExtendToSuperset phi hV.measurableSet hVW)
    _ = -∫ x in V, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by rw [hforcing]

/-! ## 3. The anchor's window: the interior gate -/

/-- A translated origin cube is open. -/
theorem isOpen_image_add_openCubeSet (z : Vec d) (k : ℤ) :
    IsOpen ((fun y => z + y) '' openCubeSet (originCube d k)) := by
  rw [← openCubeAtScale_eq_image_add z k]
  exact isOpen_openCubeAtScale z k

/-- **The anchor's equation on the parent window.**

Under the frozen theorem's own frontier-empty gate at the centre `z ∈ □_m`, the
`□_m` equation restricts to `z + □_k`: the gate gives the inclusion, and the
restriction is the general theorem above. -/
theorem isDivFormWeakSolutionOn_translateWindow_of_frontier_inter_empty {m k : ℤ}
    {z : Vec d} {a : CoeffField d} {u : H1Function (openCubeSet (originCube d m))}
    {g : Vec d → Vec d} (hz : z ∈ openCubeSet (originCube d m))
    (hfr : ((fun y => z + y) '' openCubeSet (originCube d k)) ∩
        frontier (openCubeSet (originCube d m)) = ∅)
    (h : Support.IsDivFormWeakSolutionOn a (openCubeSet (originCube d m)) u g) :
    Support.IsDivFormWeakSolutionOn a
      ((fun y => z + y) '' openCubeSet (originCube d k))
      (u.restrict (isOpen_image_add_openCubeSet z k)
        (image_add_openCubeSet_subset_of_frontier_inter_empty hz hfr)) g :=
  isDivFormWeakSolutionOn_restrict (isOpen_image_add_openCubeSet z k)
    (image_add_openCubeSet_subset_of_frontier_inter_empty hz hfr) h

/-- The same restriction driven by a bare inclusion, for callers that already
have `z + □_k ⊆ □_m` (for example from the nesting `k ≤ m` at `z = 0`, or from a
geometry binder). -/
theorem isDivFormWeakSolutionOn_translateWindow_of_subset {m k : ℤ} {z : Vec d}
    {a : CoeffField d} {u : H1Function (openCubeSet (originCube d m))}
    {g : Vec d → Vec d}
    (hsub : (fun y => z + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d m))
    (h : Support.IsDivFormWeakSolutionOn a (openCubeSet (originCube d m)) u g) :
    Support.IsDivFormWeakSolutionOn a
      ((fun y => z + y) '' openCubeSet (originCube d k))
      (u.restrict (isOpen_image_add_openCubeSet z k) hsub) g :=
  isDivFormWeakSolutionOn_restrict (isOpen_image_add_openCubeSet z k) hsub h

/-! ## 4. The convention bridge to CoarseGraining's cube predicate -/

/-- **`IsDivFormWeakSolutionOn ⟹ IsForcedEquation`, at the negated forcing.**
The two predicates carry the same equation in opposite `∇·g` conventions. -/
theorem isForcedEquation_of_isDivFormWeakSolutionOn {Q : TriadicCube d}
    {a : CoeffFamily d} {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : Support.IsDivFormWeakSolutionOn ((a.coeffOn Q).toCoeffField)
      (Ch02.cubeDomain Q : Set (Vec d)) u (fun x => -g x)) :
    IsForcedEquation Q a u g := by
  intro phi
  have hneg : ∀ x : Vec d,
      vecDot (-g x) (phi.toH1Function.grad x) =
        -vecDot (g x) (phi.toH1Function.grad x) := by
    intro x
    simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [h phi, show (fun x : Vec d => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x : Vec d => -vecDot (g x) (phi.toH1Function.grad x) from funext hneg,
    MeasureTheory.integral_neg, neg_neg]

/-- **The forcing-sign variant** consumed by the translated-frame assembly: an
unnegated `IsDivFormWeakSolutionOn` datum produces CoarseGraining's predicate
at the negated forcing. -/
theorem isForcedEquation_neg_of_isDivFormWeakSolutionOn {Q : TriadicCube d}
    {a : CoeffFamily d} {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d}
    (h : Support.IsDivFormWeakSolutionOn ((a.coeffOn Q).toCoeffField)
      (Ch02.cubeDomain Q : Set (Vec d)) u g) :
    IsForcedEquation Q a u (fun x => -g x) := by
  intro phi
  have hneg : (fun x : Vec d =>
        vecDot ((fun y : Vec d => -g y) x) (phi.toH1Function.grad x)) =
      fun x : Vec d => -vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
        -∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
            vecDot (g x) (phi.toH1Function.grad x) ∂volume := h phi
    _ = ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot ((fun y : Vec d => -g y) x) (phi.toH1Function.grad x) ∂volume := by
        rw [hneg, MeasureTheory.integral_neg]

/-- The converse bridge. -/
theorem isDivFormWeakSolutionOn_of_isForcedEquation {Q : TriadicCube d}
    {a : CoeffFamily d} {u : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    {g : Vec d → Vec d} (h : IsForcedEquation Q a u g) :
    Support.IsDivFormWeakSolutionOn ((a.coeffOn Q).toCoeffField)
      (Ch02.cubeDomain Q : Set (Vec d)) u (fun x => -g x) := by
  intro phi
  have hneg : ∀ x : Vec d,
      vecDot (-g x) (phi.toH1Function.grad x) =
        -vecDot (g x) (phi.toH1Function.grad x) := by
    intro x
    simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [h phi, show (fun x : Vec d => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x : Vec d => -vecDot (g x) (phi.toH1Function.grad x) from funext hneg,
    MeasureTheory.integral_neg, neg_neg]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
