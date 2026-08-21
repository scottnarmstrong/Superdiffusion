/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumZeroTrace
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflectionCompose

/-!
# The boundary producer at the datum-split competitor

The composition of the `hzt` supplier (`OneStepDatumZeroTrace`) with 's
met-set-agnostic boundary producer
(`Schauder.exists_classicalCompetitor_gradientHolder_boundary_zeroTrace`): for
the manuscript's odd competitor `V_odd = v − ℓ_h − v₁` at the datum reduction,
the full four-slot Schauder package on the doubled window holds with **no
zero-trace hypothesis left**: the face-only zero trace is produced from the
chain's own structural binders

* `u − h ∈ H¹₀(□_m)` (the anchor's Dirichlet datum),
* `v − u ∈ H¹₀(U₂)` (the same-boundary-data replacement),
* `v₁ − Ψ ∈ H¹₀(U₂)`, `Ψ = h − ℓ` on `U₂` (the datum corrector's trace
  structure, `OneStepDatumSplit.exists_datumCorrector`),

and the weak harmonicity of `V_odd` itself (`v`, `v₁` weakly harmonic and `ℓ`
affine — the chain's own `H¹` algebra; carried here as the packaged binder
`hvharm` on the `H¹` realization `vodd`).

After this module the reflection apparatus of the boundary branch consumes no
zero-trace input at any met configuration — interior, one-face, edge and corner
windows alike.  What remains on the boundary branch is exactly's residue (2),
the corner pricing of `oddClassDefect` (`OneStepOddClassCorner*`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec openCubeSet originCube H1Function
  LocalizedZeroTraceFunctionOn MemH10)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The boundary producer at the datum-split competitor, `hzt` discharged.**

's met-set-agnostic boundary producer applied to the manuscript's odd
competitor `V_odd = v − ℓ − v₁`, with the face-only zero trace supplied by
`localizedZeroTraceFunctionOn_datumSplit` from the chain's own binders. -/
theorem exists_classicalCompetitor_gradientHolder_boundary_datumSplit [NeZero d]
    (hd : d ≠ 0) {m n : ℤ} {x : Vec d} (hx : x ∈ openCubeSet (originCube d m))
    (hmn : n - 2 < m) {u h ℓ : Vec d → ℝ}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m (n - 2))}
    (hvu : MemH10 (truncatedWindow x m (n - 2)) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m (n - 2))}
    (hΨ : ∀ y ∈ truncatedWindow x m (n - 2), Ψ.toFun y = h y - ℓ y)
    (hv₁Ψ : MemH10 (truncatedWindow x m (n - 2))
      (fun y => v₁.toFun y - Ψ.toFun y))
    (vodd : H1Function (truncatedWindow x m (n - 2)))
    (hvharm : IsWeaklyHarmonicOn (truncatedWindow x m (n - 2)) vodd)
    (heq : ∀ y, vodd.toFun y = v.toFun y - ℓ y - v₁.toFun y)
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) c A) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] vodd.toFun ∧
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ i, IntegrableOn (fun p => gradField V p i)
          (truncatedWindow x m (n - 3)) volume) ∧
        HasGradientOn (truncatedWindow x m (n - 3)) V (gradField V) ∧
        HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K
          (gradField V) ∧
        K ≤ boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * affineExcess (truncatedWindow x m (n - 2)) V
            + boundaryOddSchauderConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ (-(n - 2)) * oddClassDefect x m n V c A) := by
  have hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m (n - 2))
      (reflectedWindow x m (n - 2)) vodd.toFun := by
    have h := localizedZeroTraceFunctionOn_datumSplit hdat hvu hΨ hv₁Ψ
    exact localizedZeroTraceFunctionOn_congr (fun y => (heq y).symm) h
  exact exists_classicalCompetitor_gradientHolder_boundary_zeroTrace hd hx hmn
    vodd hvharm hzt hodd

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
