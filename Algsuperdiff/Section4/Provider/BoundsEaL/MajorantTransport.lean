/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.DescendantLattice
import Algsuperdiff.Section4.Provider.BoundsEaL.ExpectationTransport
import Algsuperdiff.Section4.Provider.BoundsEaL.ShellSlotBounds

/-!
# The `L`-free majorant, discharged into the expectation transport

Nothing here imports that file, and nothing here claims the anchor.

## What this module does

```
Step3BlockSplit.exists_normalizedBlockResponseMax_step3_split   (the per-cube split)
  ∘ MajorantSlots.step3Display_add_negate_le_lFreeStep3Majorant (slot monotonicity)
  ∘ ShellSlotBounds.{gradient,value} slot bounds                (the shell-sum route)
  ⟹ ExpectationTransport.lintegral_observableSup_rpow_le_tsum_lintegral_moment
```

The Step-1 endpoint's per-cube object -- the block response maximum of the
flux-corrected carrier family at `σ̄_m Id` -- is bounded, uniformly in the
truncation index `L ≥ m`, by the `L`-free `lFreeStep3Majorant`; feeding that as
the transport's `G` gives the anchor's left-hand side bounded by a per-scale
`tsum` of `lintegral`s of an `L`-free integrand.

The two admissibility facts about a descendant `R ∈ desc(□_m, n−l)` that the
chain needs -- `R.scale = n − l` and `R.index ∈ 3^{R.scale} ℤ^d ∩ □_m` -- are
NOT assumed: they are the proved
`Annular.scale_eq_of_mem_descendantsAtScale_originCube` and
`Annular.index_mem_latticeCubeSet_of_mem_descendantsAtScale`.

## The one remaining input, disclosed

`hT` -- the `L`-uniform gauge of the `k > m` shell layers (see
`ShellSlotBounds.lean`, where it is stated and its status is analyzed).  It is
a conditional A obligation, not a source premise: it holds almost surely and
fails on a null set of shell sequences, because `Cutoff.CutoffSample`
constrains only the lower tails.  `hGmeas` is the transport's own measurability
side condition, carried through unchanged.

Nothing else is conditional: the constants, the split, the slot bounds and the
transport are all proved and unconditional.

## References

* ABK26, `l.bounds.mathcal.E.aL`, (statement), (Step 3), (Step 2).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Homogenization Homogenization.Book MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

/-! ## The `L`-uniform majorant of the per-cube object -/

/-- **: the `L`-free majorant, discharged.**

For every descendant `R` of `□_m` at scale `n − l` and every sample, the block
response maximum of the flux-corrected carrier family `ã_{L,m}` is bounded by
`lFreeStep3Majorant`, uniformly in `L ≥ m`.  The constant is the Section 2.4
anchor's own, taken from
`Step3BlockSplit.exists_normalizedBlockResponseMax_step3_split`.

The truncation binder `R.scale − 2 ≤ L` of Step 3's display is automatic in
range (`R.scale = n − l ≤ n ≤ m ≤ L`) and therefore does not appear.

`hT` is the single conditional obligation; see the module docstring. -/
theorem exists_normalizedBlockResponseMax_le_lFreeStep3Majorant_of_tail (d : ℕ)
    (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ), n ≤ m → ∀ s : ℝ, 0 < s → s ≤ 1 / 4 →
        M.gamma ≤ 1 / 8 →
        ∀ (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ)
          (omega : Cutoff.CutoffSample d),
          (∀ (k : ℤ) (v : Fin d → ℤ) (L : ℤ), m ≤ L →
            tailLayerSum m k v omega L ≤ T k v omega) →
          (∀ (k : ℤ) (v : Fin d → ℤ) (L : ℤ), m ≤ L →
            tailLayerSum m k v (Cutoff.negateCutoffSample omega) L ≤
              T k v (Cutoff.negateCutoffSample omega)) →
          ∀ L : ℤ, m ≤ L → ∀ (l : ℕ) (R : TriadicCube d),
            R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
              Ch02.normalizedBlockResponseMax R
                  (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
                  (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
                lFreeStep3Majorant C M m s (lFreeGradSlot m T) (lFreeValueSlot m T) R
                  omega := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hsplit⟩ := exists_normalizedBlockResponseMax_step3_split d dimension
  refine ⟨C, hC, ?_⟩
  intro M m n hnm s hs0 hs1 hgam T omega hT hTneg L hmL l R hR
  -- the descendant's two admissibility facts, from the proved index bijection
  have hlm : n - (l : ℤ) ≤ m :=
    le_trans (sub_le_self n (by exact_mod_cast Nat.zero_le l)) hnm
  have hscale : R.scale = n - (l : ℤ) :=
    scale_eq_of_mem_descendantsAtScale_originCube hlm hR
  have hv : R.index ∈ Support.latticeCubeSet d R.scale m := by
    rw [hscale]
    exact index_mem_latticeCubeSet_of_mem_descendantsAtScale hlm hR
  have hRm : R.scale ≤ m := by omega
  have hle : R.scale - 2 ≤ L := by omega
  refine le_trans (hsplit M L m R hle omega s hs0 hs1 hgam) ?_
  refine step3Display_add_negate_le_lFreeStep3Majorant hC.le M m R omega hs0 hgam
    (lFreeGradSlot m T) (lFreeValueSlot m T) (fun L' hle' hL' => ?_) (fun L' hle' hL' => ?_)
    (fun L' hle' hL' => ?_) (fun L' hle' hL' => ?_) L hle hmL
  · exact gradientW1Infinity_step3Shell_le_lFreeGradSlot M R (by omega) T omega
      (fun L'' hL'' => hT R.scale R.index L'' hL'') L' hle' hL'
  · exact gradientW1Infinity_step3Shell_le_lFreeGradSlot M R (by omega) T
      (Cutoff.negateCutoffSample omega)
      (fun L'' hL'' => hTneg R.scale R.index L'' hL'') L' hle' hL'
  · exact valueL2_step3Shell_le_lFreeValueSlot M R hRm hv T omega
      (fun L'' hL'' => hT m (0 : Fin d → ℤ) L'' hL'') L' hle' hL'
  · exact valueL2_step3Shell_le_lFreeValueSlot M R hRm hv T
      (Cutoff.negateCutoffSample omega)
      (fun L'' hL'' => hTneg m (0 : Fin d → ℤ) L'' hL'') L' hle' hL'

/-- ** in the shape of the transport's `hGmaj` slot**: the same bound with the tail
gauge required at every sample.  A corollary of the per-sample form. -/
theorem exists_normalizedBlockResponseMax_le_lFreeStep3Majorant (d : ℕ)
    (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ), n ≤ m → ∀ s : ℝ, 0 < s → s ≤ 1 / 4 →
        M.gamma ≤ 1 / 8 →
        ∀ T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ,
          (∀ (k : ℤ) (v : Fin d → ℤ) (om : Cutoff.CutoffSample d) (L : ℤ), m ≤ L →
            tailLayerSum m k v om L ≤ T k v om) →
          ∀ L : ℤ, m ≤ L → ∀ (l : ℕ) (R : TriadicCube d),
            R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
            ∀ omega : Cutoff.CutoffSample d,
              Ch02.normalizedBlockResponseMax R
                  (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
                  (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
                lFreeStep3Majorant C M m s (lFreeGradSlot m T) (lFreeValueSlot m T) R
                  omega := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hmaj⟩ :=
    exists_normalizedBlockResponseMax_le_lFreeStep3Majorant_of_tail d dimension
  refine ⟨C, hC, ?_⟩
  intro M m n hnm s hs0 hs1 hgam T hT L hmL l R hR omega
  exact hmaj M m n hnm s hs0 hs1 hgam T omega
    (fun k v L' hL' => hT k v omega L' hL')
    (fun k v L' hL' => hT k v (Cutoff.negateCutoffSample omega) L' hL') L hmL l R hR

/-! ## The transport at the `L`-free majorant -/

/-- **The anchor's left-hand side, at the `L`-free majorant.**

`ExpectationTransport.lintegral_observableSup_rpow_le_tsum_lintegral_moment` with
its `hGmaj` slot discharged by the theorem above: the `p`-th `lintegral` of the
two-argument `sup_{L ≥ m}` observable is bounded by an explicit constant times
the per-scale `tsum` of `lintegral`s of the descendant averages of
`lFreeStep3Majorant^{p/2}` -- an integrand that does not mention `L`.

`hT` (the shell-tail gauge) and `hGmeas` (the transport's measurability side
condition, stated at this very majorant) are the two caller obligations. -/
theorem lintegral_observableSup_rpow_le_tsum_lintegral_lFreeStep3Majorant (d : ℕ)
    (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ), n ≤ m → ∀ (s : {s : ℝ // 0 < s}),
        (s : ℝ) ≤ 1 / 4 → M.gamma ≤ 1 / 8 →
        ∀ p : ℝ, 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p →
        ∀ T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ,
          (∀ (k : ℤ) (v : Fin d → ℤ) (om : Cutoff.CutoffSample d) (L : ℤ), m ≤ L →
            tailLayerSum m k v om L ≤ T k v om) →
          (∀ l : ℕ, Measurable fun omega =>
            Ch02.finsetAverageReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
              (fun R => Real.rpow
                (lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m T) (lFreeValueSlot m T) R
                  omega) (p / 2))) →
          (∫⁻ omega, Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p
              ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
            ENNReal.ofReal (Real.rpow (2 : ℝ) p *
                Real.rpow (3 : ℝ) (1 / 2 * p * (s : ℝ) * ((m : ℝ) - (n : ℝ))) *
                Ch02.geometricDiscount (s : ℝ) 1) *
              ∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s : ℝ) * (l : ℝ))) *
                ∫⁻ omega, ENNReal.ofReal
                    (Ch02.finsetAverageReal
                      (descendantsAtScale (originCube d m) (n - (l : ℤ)))
                      (fun R => Real.rpow
                        (lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m T)
                          (lFreeValueSlot m T) R omega) (p / 2)))
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hmaj⟩ := exists_normalizedBlockResponseMax_le_lFreeStep3Majorant d dimension
  refine ⟨C, hC, ?_⟩
  intro M m n hnm s hs1 hgam p hp T hT hGmeas
  refine lintegral_observableSup_rpow_le_tsum_lintegral_moment M hnm s
    (le_trans hs1 (by norm_num)) hp
    (fun _ R omega =>
      lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m T) (lFreeValueSlot m T) R omega)
    hGmeas ?_
  intro L hL l R hR omega
  exact hmaj M m n hnm (s : ℝ) s.2 hs1 hgam T hT L hL l R hR omega

end

end Algsuperdiff.Section4.Provider.BoundsEaL
