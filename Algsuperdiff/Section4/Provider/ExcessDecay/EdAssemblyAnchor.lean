/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyLegs
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEntry
import Algsuperdiff.Section4.Provider.ExcessDecay.ProviderEpsFree
import Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# The anchor A at the one-step window choice

The harmonic-approximation anchor this module applies is the proved, sorry-free
provider theorem
`Algsuperdiff.Section4.Provider.ExcessDecay.harmonic_approximation_provider_epsFree`
(`ProviderEpsFree`), which depends on exactly the standard triple.  It is
*imported and applied* here, and that is all this module does.

## The instantiation

The anchor is read at the excess-decay consumer's own window choice,

```text
  x := wellPlacedCentre x m (n-2) ,   n := n - 2 ,   z := z ,   m := m ,  L := L ,
```

i.e. at the clamped centre `y` of `OneStepWindows`, whose cube is the
`movedReplacementCube`.  The two geometric obligations of the anchor are
discharged, not assumed:

* `y ∈ □_m` from `image_add_wellPlacedCentre_subset_openCubeSet`;

Every index below is written **as the anchor prints it after the substitution**:
the good-event and flux index is `n - 2 + 3`, the display windows are
`(z+□_{n-2+3}) ∩ □_m` and `(z+□_{n-2+2}) ∩ □_m`, the `σ̄` index is `n - 2`, and
the `3`-powers are at `(n-2 : ℤ)`.  These are literally the indices the nine
`_regated` one-step siblings' `hharm` slots read.

## What is delivered

A single existential package `⟨B, hB, hharm, hexp⟩` per `ω`:

* `hB : B ≠ ⊤` — the one-step consumers' own finiteness slot, discharged from
  the anchor's clause-(iv) `MemLp` binders and the `H¹` data of `u` and `h`;
* `hharm` — the anchor's per-`ω` display, *verbatim* in the shape the `_regated`
  siblings consume (the re-gated good event, the moved-cube carrier);
* `hexp : B.toReal ≤ …` — **the `B.toReal` expansion** into the anchor's four
  printed legs (oscillation with the in-bracket `∇h` companion, force Besov,
  `∇h` Besov, `∇h` `L̲²`), which is `OneStepConditional`'s disclosed
  §4.4-collapse residue.

Packaging the three as one existential is what keeps the anchor's (large)
display from being written twice: `B` is instantiated by unification against the
anchor's own right-hand side.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the anchor);
  `l.excess.decay.good.scales`, and its proof's window-choice and
  harmonic-approximation steps.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory
open scoped ENNReal

noncomputable section

/-- **The harmonic-approximation anchor, applied at the one-step window choice.**

For a.e. `ω`, every Dirichlet datum on `□_m` and every harmonic replacement on
the moved cube `y + □_{n-2}`, the anchor's general clause is available as a
finite bound `B` on the good-event-gated indicator, together with the expansion of
`B.toReal` into the four printed legs. -/
theorem exists_oneStepAnchorBound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n - 2 + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ truncatedWindow z m (n - 3) →
            z ∈ openCubeSet (originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
                IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (originCube d m) u hdat g →
                MemLp g 2
                    (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                ∀ (v : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                        openCubeSet (originCube d (n - 2))))
                  (w : H10Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                        openCubeSet (originCube d (n - 2)))),
                  IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                    openCubeSet (originCube d (n - 2))) v →
                  (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                  (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                  ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
                    Set.indicator
                        (Algsuperdiff.Frozen.Section4.goodEventAt M
                          (cgEllipLowerConstant d) (n - 2 + 3) z
                          ⟨s / 8, by linarith only [hs]⟩ (C⁻¹ * s ^ (4 : ℕ)))
                        (fun _omega' =>
                          MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                            (normalizedVolumeMeasureOn
                              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                                openCubeSet (originCube d (n - 2)))))
                        omega ≤ B ∧
                    B.toReal ≤
                      C * Real.rpow s (-(4 : ℝ)) *
                          fluxCorrectedErrorRepresentative M L (n - 2 + 3)
                            ⟨s / 8, by linarith only [hs]⟩
                            (Cutoff.translateCutoffSample z omega) *
                          ((MeasureTheory.eLpNorm
                              (fun y => u.toFun y -
                                Homogenization.volumeAverage
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n - 2 + 3))) ∩
                                    openCubeSet (originCube d m)) u.toFun) 2
                              (normalizedVolumeMeasureOn
                                (((fun y' => z + y') ''
                                    openCubeSet (originCube d (n - 2 + 3))) ∩
                                  openCubeSet (originCube d m)))).toReal +
                            Real.rpow s (-(3 / 2 : ℝ)) *
                                Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                              ‖Homogenization.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n - 2 + 2))) ∩
                                    openCubeSet (originCube d m)) hdat.grad‖) +
                        C * Real.rpow s (-(7 : ℝ)) *
                            (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
                            Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                          (normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                openCubeSet (originCube d (n - 2 + 3))) ∩
                              openCubeSet (originCube d m)) s g).toReal +
                        C * Real.rpow s (-(6 : ℝ)) *
                            Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                          (normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                openCubeSet (originCube d (n - 2 + 3))) ∩
                              openCubeSet (originCube d m)) s hdat.grad).toReal +
                        C * Real.rpow s (-(6 : ℝ)) *
                            Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                          (MeasureTheory.eLpNorm hdat.grad 2
                            (normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  openCubeSet (originCube d (n - 2 + 3))) ∩
                                openCubeSet (originCube d m)))).toReal := by
  classical
  obtain ⟨C, hC, hclause⟩ :=
    Algsuperdiff.Section4.Provider.ExcessDecay.harmonic_approximation_provider_epsFree d
  refine ⟨C, hC, ?_⟩
  intro M s hsrange hregime hfund hs L m n hmL hnm x z hxz hz
  have hnm2 : n - 2 ≤ m := by omega
  have hym : wellPlacedCentre x m (n - 2) ∈ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet x hnm2
      ⟨0, zero_mem_openCubeSet_originCube d (n - 2), by simp⟩
  have hgeom : (fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n - 2 + 1))) ∩
        openCubeSet (originCube d m) := by
    have h := image_add_wellPlacedCentre_subset_windowChoice hxz hnm2
    rw [truncatedWindow] at h
    rw [show n - 2 + 1 = n - 1 by ring]
    exact h
  -- the two display windows and their volumes, at the anchor's own indices
  have hWtop := volume_anchorWindow_ne_top (n - 2 + 3) m z
  have hW20 : volume ((((fun y' => z + y') ''
      openCubeSet (originCube d (n - 2 + 2))) ∩
      openCubeSet (originCube d m))) ≠ 0 := volume_anchorWindowInner_ne_zero hgeom
  have hW30 : volume ((((fun y' => z + y') ''
      openCubeSet (originCube d (n - 2 + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 := by
    intro hzero
    have hmono := measure_mono (μ := (volume : Measure (Vec d)))
      (anchorWindowInner_subset_anchorWindow (d := d) (n - 2) m z)
    rw [hzero, le_zero_iff] at hmono
    exact hW20 hmono
  haveI := isProbabilityMeasure_normalizedVolumeMeasureOn hW30 hWtop
  -- the sign data of the four printed coefficients
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M (n - 2)).2.le
  filter_upwards [hclause M s hsrange hregime hfund hs L m (n - 2) hmL hnm
    (wellPlacedCentre x m (n - 2)) z hym hz hgeom] with omega hom
  intro u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  obtain ⟨hgen, -⟩ := hom u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  -- the anchor's clause (iv) and `H¹` data, read on the display window
  have hum : MemLp u.toFun 2
      (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) u.memL2
  have hhm : MemLp hdat.grad 2
      (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) hdat.grad_memVectorL2
  have hu3 : MemLp u.toFun 2
      (normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n - 2 + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hum
  have hh3 : MemLp hdat.grad 2
      (normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n - 2 + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hhm
  have hg3 : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n - 2 + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hgW
  have hgh3 : MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
      (normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n - 2 + 3))) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW30 hhW
  refine ⟨_, ofReal_mul_bracket_add_three_ne_top
    (hu3.sub (memLp_const _)).eLpNorm_ne_top hg3.eLpNorm_ne_top hgh3.eLpNorm_ne_top
    hh3.eLpNorm_ne_top, hgen, ?_⟩
  exact toReal_ofReal_mul_bracket_add_three_le _ _ _ _
    (mul_nonneg (mul_nonneg hC.le hS4)
      (fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _))
    (mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hS7) hsgn) h3sn)
    (mul_nonneg (mul_nonneg hC.le hS6) h3sn)
    (mul_nonneg (mul_nonneg hC.le hS6) h3n)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
