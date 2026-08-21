/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenSandwich
import Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportAssembly

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The transport at a generic scale, off the bare inclusion -/

/-- **The equation on `c + □_k`, transported to `□_k`, with NO interior gate.**

`ExcessDecay.isForcedEquation_fluxCorrectedCoeffFamily_translated` at a generic
scale `k` and with the frozen theorem's frontier-empty gate replaced by the
bare inclusion `translateSet c □_k ⊆ □_m`.  Every step is the proved one: the
restriction to an open subset, the A4 untranslation of the cutoff sample, the
antisymmetric flux shift, and the `IsDivFormWeakSolutionOn ⟹ IsForcedEquation`
convention bridge at the negated forcing. -/
theorem isForcedEquation_fluxCorrected_of_subset {m k : ℤ}
    (M : ABKModel d) (L : ℤ) (c : Vec d) (omega : Cutoff.CutoffSample d)
    {u : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsub : translateSet c (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m))
    (heq : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (openCubeSet (originCube d m)) u g) :
    IsForcedEquation (originCube d k)
      (Support.fluxCorrectedCoeffFamily M L k (originCube d k)
        (Cutoff.translateCutoffSample c omega))
      (H1Function.untranslate c
        (u.restrict (isOpen_translateSet_openCubeSet c k) hsub))
      (fun x => -g (x + c)) := by
  have hrestrict := isDivFormWeakSolutionOn_restrict
    (isOpen_translateSet_openCubeSet c k) hsub heq
  have huntrans := isDivFormWeakSolutionOn_translateCutoffSample M L c omega hrestrict
  have hshift := isDivFormWeakSolutionOn_fluxCorrectedField M L k
    (originCube d k) (Cutoff.translateCutoffSample c omega) huntrans
  refine isForcedEquation_neg_of_isDivFormWeakSolutionOn ?_
  rw [fluxCorrectedCoeffFamily_coeffOn_toCoeffField M L k
    (originCube d k) (originCube d k) (Cutoff.translateCutoffSample c omega)]
  exact hshift

/-- The same, entered at `t.regularity` Step 3's own `IsDirichletSolutionOn` datum. -/
theorem isForcedEquation_fluxCorrected_of_isDirichletSolutionOn {m k : ℤ}
    (M : ABKModel d) (L : ℤ) (c : Vec d) (omega : Cutoff.CutoffSample d)
    {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsub : translateSet c (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m))
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g) :
    IsForcedEquation (originCube d k)
      (Support.fluxCorrectedCoeffFamily M L k (originCube d k)
        (Cutoff.translateCutoffSample c omega))
      (H1Function.untranslate c
        (u.restrict (isOpen_translateSet_openCubeSet c k) hsub))
      (fun x => -g (x + c)) :=
  isForcedEquation_fluxCorrected_of_subset M L c omega hsub hsol.2

/-! ## 2. The builder, at every centre of `□_m` -/

/-- ** gap 6: the boundary `ForcedCubeSolution` builder.**

```text
   (z + □_k) ∩ □_m  ⊆  c + □_k  ⊆  (z + □_{k+1}) ∩ □_m
```

and a `ForcedCubeSolution` on `□_k` for the flux-corrected family at the
translated sample, whose values are `u(· + c)`.  These are exactly the four
binders `exists_stepSevenEnd_chain_of_caps` opens with (`u`, the pointwise
identity at `w := u.toFun`, `hz`/`hkm`, and `hST`).

The centre `c` is in general O the triadic lattice; the caller must supply the
A6 caps there (stop (i)). -/
theorem exists_boundaryForcedCubeSolution {m k : ℤ}
    (M : ABKModel d) (L : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d)
    {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hkm : k ≤ m)
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g) :
    ∃ c : Vec d, c ∈ openCubeSet (originCube d m) ∧
      truncatedWindow z m k ⊆ (fun v => c + v) '' openCubeSet (originCube d k) ∧
      (fun v => c + v) '' openCubeSet (originCube d k) ⊆ truncatedWindow z m (k + 1) ∧
      ∃ w : ForcedCubeSolution (originCube d k)
          (Support.fluxCorrectedCoeffFamily M L k (originCube d k)
            (Cutoff.translateCutoffSample c omega))
          (fun x => -g (x + c)),
        ∀ y : Vec d, w.toH1.toFun y = u.toFun (y + c) := by
  obtain ⟨c, hcm, hin, hout⟩ := exists_sandwich_centre z hz hkm
  have hsub : translateSet c (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d m) := by
    rw [← image_add_eq_translateSet c (openCubeSet (originCube d k))]
    exact hout.trans (truncatedWindow_subset_domain z m (k + 1))
  refine ⟨c, hcm, hin, hout,
    ⟨H1Function.untranslate c (u.restrict (isOpen_translateSet_openCubeSet c k) hsub),
      isForcedEquation_fluxCorrected_of_isDirichletSolutionOn M L c omega hsub hsol⟩,
    ?_⟩
  intro y
  exact untranslate_restrict_toFun u hsub y

end

end Algsuperdiff.Section4.Provider.Regularity
