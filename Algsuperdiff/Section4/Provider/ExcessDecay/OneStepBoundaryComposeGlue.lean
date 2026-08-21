/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumZeroTraceCompose
import Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitHarmonic
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepTriangle

/-!
# The two structural glues of the boundary composition

Two mechanical pieces the boundary branch's assembly needs, and nothing else.

## 1. The `H¹` algebra of the manuscript competitor

`OneStepDatumZeroTraceCompose.exists_classicalCompetitor_gradientHolder_boundary_datumSplit`
takes the manuscript's odd competitor `V_odd = v − ℓ_h − v₁` as a *packaged*
`H¹` realization `vodd` together with its weak harmonicity `hvharm` and the
packaging identity `heq`.  Both are supplied here from the chain's own data by
the proved `H¹` algebra: `H1Function` is an `AddCommGroup`
(`Homogenization.H1Function.sub_toFun`/`sub_grad`), weak harmonicity is
subtractive (`AffineSplitHarmonic.isWeaklyHarmonicOn_sub`) and the affine lift
is weakly harmonic because its weak gradient is constant
(`AffineSplitHarmonic.isWeaklyHarmonicOn_affineLiftH1`).  No analytic input.

## 2. The affine-minimizer datum at the consumption window

The odd-class apparatus consumes `IsAffineMinimizer U₂ V (c − A·x) A`.  On a
truncated window this is a **theorem**, not a hypothesis: the window carries the
axis-cube sandwich, hence the two-sided affine nondegeneracy, hence attainment
(`SandwichNondegeneracyAttainment` through
`OneStepTriangle.exists_isAffineMinimizer_truncatedWindow`).  The only work here
is the change of affine parametrization `(c₀, g) ↦ (c₀ + g·x, g)` that puts the
minimizer in the `(c − A·x, A)` display the boundary producers print.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec vecDot openCubeSet originCube H1Function MemH10)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `H¹` glue: the packaged competitor `v − ℓ_h − v₁` -/

/-- **The manuscript competitor as an `H¹` datum.**

`V_odd = v − ℓ_h − v₁` is realized in `H¹(U₂)`, is weakly harmonic there, and
has the packaging identity, purely from the `H¹` algebra: `v` and `v₁` are
weakly harmonic by hypothesis and the affine lift `ℓ_h` is weakly harmonic
because its weak gradient is the constant `A_ℓ`. -/
theorem exists_h1_oddCompetitor_affineSplit {m k : ℤ} {x : Vec d}
    {v v₁ : H1Function (truncatedWindow x m k)}
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hv₁ : IsWeaklyHarmonicOn (truncatedWindow x m k) v₁) (cl : ℝ) (Al : Vec d) :
    ∃ vodd : H1Function (truncatedWindow x m k),
      IsWeaklyHarmonicOn (truncatedWindow x m k) vodd ∧
      ∀ y, vodd.toFun y = v.toFun y - affineLift x cl Al y - v₁.toFun y := by
  haveI : IsFiniteMeasure (Homogenization.volumeMeasureOn (truncatedWindow x m k)) :=
    (isOpenBoundedConvexDomain_truncatedWindow x m k).isFiniteMeasure_restrict_volume
  set hSob := (isOpenBoundedConvexDomain_truncatedWindow x m k).isSobolevRegularDomain
    with hSobdef
  set l : H1Function (truncatedWindow x m k) := affineLiftH1 hSob x cl Al with hldef
  refine ⟨v - l - v₁, ?_, ?_⟩
  · exact isWeaklyHarmonicOn_sub
      (isWeaklyHarmonicOn_sub hv (isWeaklyHarmonicOn_affineLiftH1 hSob x cl Al)) hv₁
  · intro y
    have hl : l.toFun y = affineLift x cl Al y := by
      rw [hldef, affineLiftH1_toFun]
    simp only [Homogenization.H1Function.sub_toFun]
    rw [hl]

/-- **The boundary producer at the manuscript competitor, `hzt` discharged and
the `H¹` packaging supplied.**

`exists_classicalCompetitor_gradientHolder_boundary_datumSplit` with its two
packaged binders `hvharm`/`heq` produced from the chain's own weak harmonicity
of the replacement `v` and of the datum corrector `v₁`.  The boundary branch's
Schauder package now depends on no packaging input at all. -/
theorem exists_classicalCompetitor_gradientHolder_boundary_affineSplit [NeZero d]
    (hd : d ≠ 0) {m n : ℤ} {x : Vec d} (hx : x ∈ openCubeSet (originCube d m))
    (hmn : n - 2 < m) {u h : Vec d → ℝ}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m (n - 2))}
    (hvharm : IsWeaklyHarmonicOn (truncatedWindow x m (n - 2)) v)
    (hvu : MemH10 (truncatedWindow x m (n - 2)) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m (n - 2))}
    (hv₁harm : IsWeaklyHarmonicOn (truncatedWindow x m (n - 2)) v₁)
    {cl : ℝ} {Al : Vec d}
    (hΨ : ∀ y ∈ truncatedWindow x m (n - 2),
      Ψ.toFun y = h y - affineLift x cl Al y)
    (hv₁Ψ : MemH10 (truncatedWindow x m (n - 2))
      (fun y => v₁.toFun y - Ψ.toFun y))
    {c : ℝ} {A : Vec d} (hodd : IsOddAffineData x m (n - 2) c A) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))]
        (fun y => v.toFun y - affineLift x cl Al y - v₁.toFun y) ∧
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
  obtain ⟨vodd, hvoddharm, heq⟩ :=
    exists_h1_oddCompetitor_affineSplit hvharm hv₁harm cl Al
  obtain ⟨V, hVharm, hVmem, hVae, hK⟩ :=
    exists_classicalCompetitor_gradientHolder_boundary_datumSplit hd hx hmn hdat hvu
      hΨ hv₁Ψ vodd hvoddharm heq hodd
  refine ⟨V, hVharm, hVmem, ?_, hK⟩
  filter_upwards [hVae] with y hy
  rw [hy, heq y]

/-! ## 2. The affine-minimizer datum at the consumption window -/

/-- **`hmin` at consumption.**  On the truncated window the affine minimum is
attained, in the `(c − A·x, A)` parametrization the boundary producers print. -/
theorem exists_isAffineMinimizer_shifted_truncatedWindow {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {V : Vec d → ℝ}
    (hV : MemLp V 2 (volume.restrict (truncatedWindow x m k))) :
    ∃ (c : ℝ) (A : Vec d),
      IsAffineMinimizer (truncatedWindow x m k) V (c - vecDot A x) A := by
  obtain ⟨c₀, g, hmin⟩ := exists_isAffineMinimizer_truncatedWindow hx hkm hV
  refine ⟨c₀ + vecDot g x, g, ?_⟩
  have hc : c₀ + vecDot g x - vecDot g x = c₀ := by ring
  rw [hc]
  exact hmin

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
