/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdFinalInputs
import Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestriction

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Weak harmonicity restricts to open subsets -/

/-- The zero extension of an `H¹₀(V)` test gradient integrates against any
vector field over `W` exactly as it does over `V`.  A local re-derivation of the
`private` step behind `EquationRestriction.isDivFormWeakSolutionOn_restrict`,
needed here because that step is not exported. -/
private theorem setIntegral_vecDot_h10Extend {V W : Set (Vec d)}
    (hV : MeasurableSet V) (hVW : V ⊆ W) (F : Vec d → Vec d) (phi : H10Function V) :
    ∫ x in W, vecDot (F x)
        ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x) ∂volume =
      ∫ x in V, vecDot (F x) (phi.toH1Function.grad x) ∂volume := by
  have hindicator :
      (fun x => vecDot (F x)
          ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x)) =
        Set.indicator V (fun x => vecDot (F x) (phi.toH1Function.grad x)) := by
    funext x
    by_cases hx : x ∈ V
    · simp only [h10ExtendToSuperset_grad, h10ZeroExtensionGrad_of_mem phi hx,
        Set.indicator_of_mem hx]
    · simp only [h10ExtendToSuperset_grad, h10ZeroExtensionGrad_of_not_mem phi hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  rw [hindicator, MeasureTheory.integral_indicator hV,
    Measure.restrict_restrict hV, Set.inter_eq_left.mpr hVW]

/-- **Weak harmonicity restricts to every open subset.**

If `v` is weakly harmonic on `W` and `V ⊆ W` is open, the restriction of `v` is
weakly harmonic on `V`: every test function of `H¹₀(V)` extends by zero to one
of `H¹₀(W)`. -/
theorem isWeaklyHarmonicOn_restrict {W V : Set (Vec d)} (hV : IsOpen V)
    (hVW : V ⊆ W) {v : H1Function W} (h : IsWeaklyHarmonicOn W v) :
    IsWeaklyHarmonicOn V (v.restrict hV hVW) := by
  intro phi
  have hext := setIntegral_vecDot_h10Extend hV.measurableSet hVW v.grad phi
  have hgradEq : (v.restrict hV hVW).grad = v.grad := rfl
  calc
    ∫ x in V, vecDot ((v.restrict hV hVW).grad x) (phi.toH1Function.grad x) ∂volume =
        ∫ x in W, vecDot (v.grad x)
          ((h10ExtendToSuperset phi hV.measurableSet hVW).toH1Function.grad x)
          ∂volume := by
          rw [hgradEq, hext]
    _ = 0 := h (h10ExtendToSuperset phi hV.measurableSet hVW)

/-! ## 2. The harmonic replacement pair ON the §4.4 window -/

/-- `EdFinalInputs.exists_harmonicReplacementPair_movedCube` is stated at the index
`n - 2`; this is the same statement with the clamped cube's own scale `j` free,
which is what the one-scale enlargement below needs. -/
theorem exists_harmonicReplacementPair_clampedCube [NeZero d] {m j : ℤ} (z : Vec d)
    (hjm : j ≤ m) (u : H1Function (openCubeSet (originCube d m))) :
    ∃ (v : H1Function ((fun y => wellPlacedCentre z m j + y) ''
          openCubeSet (originCube d j)))
      (w : H10Function ((fun y => wellPlacedCentre z m j + y) ''
          openCubeSet (originCube d j))),
      IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m j + y) ''
          openCubeSet (originCube d j)) v ∧
        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) ∧
        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) := by
  have h := exists_harmonicReplacementPair_movedCube (m := m) (n := j + 2) (z := z)
    (by omega : j + 2 - 2 ≤ m) u
  rwa [show j + 2 - 2 = j from by ring] at h

/-- **The `U₂` carrier seam, closed.**

The `H¹₀` corrector `w` stays on the enlarged clamped cube, where it is
produced; the two pointwise identities of the pair are unchanged (the
restriction shares `toFun` and `grad` definitionally). -/
theorem exists_harmonicReplacementPair_truncatedWindow [NeZero d] {m n : ℤ}
    {z : Vec d} (hnm : n - 1 ≤ m) (u : H1Function (openCubeSet (originCube d m))) :
    ∃ (v : H1Function (truncatedWindow z m (n - 2)))
      (w : H10Function ((fun y => wellPlacedCentre z m (n - 1) + y) ''
          openCubeSet (originCube d (n - 1)))),
      IsWeaklyHarmonicOn (truncatedWindow z m (n - 2)) v ∧
        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) ∧
        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) := by
  obtain ⟨v, w, hharm, hval, hgrad⟩ :=
    exists_harmonicReplacementPair_clampedCube (m := m) (j := n - 1) z hnm u
  have hsub : truncatedWindow z m (n - 2) ⊆
      (fun y => wellPlacedCentre z m (n - 1) + y) '' openCubeSet (originCube d (n - 1)) :=
    truncatedWindow_subset_image_add_wellPlacedCentre z hnm (by omega : n - 2 ≤ n - 1)
  have hopen : IsOpen (truncatedWindow z m (n - 2)) := isOpen_truncatedWindow z m (n - 2)
  exact ⟨v.restrict hopen hsub, w, isWeaklyHarmonicOn_restrict hopen hsub hharm,
    hval, hgrad⟩

end

end Algsuperdiff.Section4.Provider.Regularity
