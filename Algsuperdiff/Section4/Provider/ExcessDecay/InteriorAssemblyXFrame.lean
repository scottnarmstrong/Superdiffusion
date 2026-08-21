/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.InteriorAssemblyLhs
import Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueWindow

/-!
# The interior clause, composed in the child's own frame

```text
  σ 3^{-n} ‖u − v‖_{L̲²(x+□_n)}
      ≤ 3 C_neg(d) C_cg(d) ( (1024/3) s^{-4} · 𝓔-energy term
                           + (16384/3) s^{-6} · forcing term )
      + C_corr(d) s^{-1/2} 3^{sn} [g]_{H̲^s(x+□_n)} ,
```

for **every** pair `(v, w)` the anchor quantifies over, every `σ > 0`, and every
sample `ω` — no probability enters here.

## What is composed

* the equation: the anchor's Dirichlet datum on `□_m`, restricted to `x + □_n`,
  untranslated to the child's own frame, and shifted by the child's own
  antisymmetric flux increment (`childFluxCorrectedFamily`);
* the left-hand side: `InteriorAssemblyLhs`'s identification of the anchor's
  quantified `v` with the constructed harmonic replacement;
* the correction summand: `InteriorGlue`'s `correctionLeg_le_anchorGagliardo`
  (+), which proves it in the anchor's own Gagliardo carrier at the honest
  `s^{-1/2}`.

## The exact distance to the frozen statement (reported, not hidden)

Three conversions remain between this bound and the anchor's interior clause,
all of them on the **right-hand side**:

1. the coarse-graining error object `𝓔_{s/4,∞,1}(□_n; ã_x, σ Id)` of the
   child's own frame must become the anchor's
   `fluxCorrectedErrorRepresentative` at the parent — the proved off-grid cap
   (`InteriorGlueCap`) is stated for the *parent-frame* off-grid functional, so
   the missing step is the translation covariance of
   `Homogenization.ResponseJ`, which is **not** proved;
2. the coarse-grained ellipticity factors `λ_{s/8,2}`, `Λ_{s/8,2}` inside the
   forcing bracket must be capped on the good event — the proved caps
   (`GoodEventCaps`, `SlotTransportChildCube`) live at grid cubes in the
   parent's frame, so the same covariance is required;

None of the three is assumed anywhere in this module.

## References

* ABK26, `l.harmonic.approximation.good.scales`;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The child's own flux-corrected family -/

/-- **The child cube's flux-corrected coefficient family, in the child's own
frame.**  The cutoff coefficient at the translated sample
`translateCutoffSample x ω`, minus its own antisymmetric flux increment over
`□_n`. -/
def childFluxCorrectedFamily (M : ABKModel d) (L n : ℤ) (x : Vec d)
    (omega : Cutoff.CutoffSample d) : Ch03.CoeffFamily d :=
  Support.fluxCorrectedCoeffFamily M L n (originCube d n)
    (Cutoff.translateCutoffSample x omega)

/-- **The equation in the child's own frame.** -/
theorem isForcedEquation_childFluxCorrectedFamily {n m : ℤ} (M : ABKModel d)
    (L : ℤ) (x : Vec d) (omega : Cutoff.CutoffSample d)
    {u : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsub : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (heq : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (openCubeSet (originCube d m)) u g) :
    Ch03.IsForcedEquation (originCube d n) (childFluxCorrectedFamily M L n x omega)
      (H1Function.untranslate x
        (u.restrict (isOpen_translateSet_openCubeSet x n) hsub))
      (fun y => -g (y + x)) := by
  have hrestrict := isDivFormWeakSolutionOn_restrict
    (isOpen_translateSet_openCubeSet x n) hsub heq
  have huntrans := isDivFormWeakSolutionOn_translateCutoffSample M L x omega hrestrict
  have hshift := isDivFormWeakSolutionOn_fluxCorrectedField M L n (originCube d n)
    (Cutoff.translateCutoffSample x omega) huntrans
  refine isForcedEquation_neg_of_isDivFormWeakSolutionOn ?_
  rw [childFluxCorrectedFamily,
    fluxCorrectedCoeffFamily_coeffOn_toCoeffField M L n (originCube d n)
      (originCube d n) (Cutoff.translateCutoffSample x omega)]
  exact hshift

/-! ## 2. The composed interior bound -/

variable [NeZero d]

/-- **The interior clause's left-hand side, bounded in the child's own frame.**

Every constant is explicit and `d`-only; the correction leg's `s`-power is the
honest `−1/2`.  See the module docstring for the three conversions that separate
this bound from the frozen statement's right-hand side. -/
theorem eLpNorm_sub_weaklyHarmonic_le_coarseGraining_xFrame (M : ABKModel d)
    (L : ℤ) (omega : Cutoff.CutoffSample d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {n m : ℤ} {x : Vec d}
    (hsub : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g)
    (hgL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
    (v : H1Function ((fun y => x + y) '' openCubeSet (originCube d n)))
    (w : H10Function ((fun y => x + y) '' openCubeSet (originCube d n)))
    (hharm : Support.IsWeaklyHarmonicOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) v)
    (hval : ∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y)
    (hgrad : ∀ y, v.grad y = u.grad y - w.toH1Function.grad y)
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) (originCube d n) *
        (eLpNorm (fun y => u.toFun y - v.toFun y) 2
          (Support.normalizedVolumeMeasureOn
            ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal) ≤
      3 * negNormBaseConst d * coarseGrainingP2Const d *
          ((1024 / 3) * (s⁻¹) ^ (4 : ℕ) *
              coarseGrainingEnergyTerm (originCube d n)
                (childFluxCorrectedFamily M L n x omega) (scalarComparator hsigma0)
                (s / 4)
                (H1Function.untranslate x
                  (u.restrict (isOpen_translateSet_openCubeSet x n) hsub)) +
            (16384 / 3) * (s⁻¹) ^ (6 : ℕ) *
              coarseGrainingForceTerm (originCube d n)
                (childFluxCorrectedFamily M L n x omega) (scalarComparator hsigma0)
                (s / 4) s (fun y => -g (y + x))) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
          Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (Support.normalizedGagliardoESeminormOn
            ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
  have hsubimg : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := by
    rw [image_add_eq_translateSet x (openCubeSet (originCube d n))]
    exact hsub
  -- clause (iv) at the child window
  have hgL2child := memLp_two_child_of_clause_iv hsubimg hgL2
  have hgWchild := memLp_two_gagliardo_child_of_clause_iv hsubimg hgW
  have hforce : Ch03.ForceBesovRegularity (originCube d n) s (fun y => -g (y + x)) :=
    forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild
  -- the equation in the child's own frame
  have heq := isForcedEquation_childFluxCorrectedFamily M L x omega hsub hsol.2
  -- the harmonic display
  have hmain := coarseGraining_l2_slot_harmonic_le hsigma0 heq hs hs1 hforce
  -- the left-hand side, in the anchor's carriers
  have hlhs : cubeLpNorm (originCube d n) (2 : ℝ≥0∞)
      (fun y =>
        (harmonicCorrector (scalarComparator hsigma0)
          (H1Function.untranslate x
            (u.restrict (isOpen_translateSet_openCubeSet x n) hsub))).toH1Function.toFun
          y) =
      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal := by
    show (eLpNorm _ (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d n))).toReal = _
    exact congrArg ENNReal.toReal
      (eLpNorm_sub_weaklyHarmonic_eq_harmonicCorrector hsigma0
        (image_add_eq_translateSet x (openCubeSet (originCube d n))) hsub u v w hharm
        hval hgrad).symm
  rw [hlhs] at hmain
  refine hmain.trans (add_le_add le_rfl ?_)
  exact correctionLeg_le_anchorGagliardo n hs hs1 hgL2child hgWchild

end

end Algsuperdiff.Section4.Provider.ExcessDecay
