/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyOneStep
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryFullRegated

/-!
# The boundary branch off the anchor, and the JOIN

One theorem.

* `excessDecay_oneStep_anchored` — **the join**: one statement covering every
  scale-`n` window, interior gate **or** at least one met face in either
  orientation, at the single constant `max (schauderWindowConst d) C_bdry`.
  Its boundary branch is the re-gated met-set endpoint
  `OneStepBoundaryFullRegated.excessDecay_oneStep_boundary_metSet_of_harmonicApprox_regated`,
  with its `hharm`/`hB` slots discharged from the anchor and its `B.toReal`
  expanded, exactly as the interior branch of `EdAssemblyOneStep`.

## What the boundary branch still carries, and why that is the proved contract

They are therefore carried, not smuggled: nothing here re-derives or assumes an
estimate.  The competitor is the anchor's own `v.toFun`, so no
`a.e.`-representative move is performed at this seam either.

## The join's constant

`triangleRemainderConst d C k = 81 C_t(d) C + 9·3^k √((3^k)^d)` and the
contraction prefactor `C_t(d) C κ(d)` are both nondecreasing in `C`
(`EdAssemblyOneStep.oneStepConclusion_mono`), so both branches are raised to
`max (schauderWindowConst d) C_bdry` with no other move.  Neither the
`3^{-k/2}` rate nor the remainder's `3^{-n}·3^d` weight changes.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

/-! ## 1. The composed boundary one-step, and the join -/

/-- **The one-step excess-decay contraction off the anchor, at every scale-`n`
window: interior gate OR at least one met face.**

The window hypothesis is the disjunction

```text
  (x + □_{n-2}) ⊆ □_m        (the interior gate)
   ∨   the window meets a face of ∂□_m in either orientation,
       with the anchor's own competitor `v` classically harmonic and met-face
       odd on the doubled window (ED-U's binders, produced by ED-R's chain).
``` -/
theorem excessDecay_oneStep_anchored (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Cb : ℝ, 0 < C ∧ 0 ≤ Cb ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ delta : ℝ, delta ≤ 1 → delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * s ^ (6 : ℕ) →
        ∀ L m n : ℤ, m ≤ L → n - 2 + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ truncatedWindow z m (n - 3) →
            z ∈ openCubeSet (originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (cgEllipLowerConstant d) (n - 2 + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (s / 8 * Real.sqrt delta) →
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
                    ((fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
                        openCubeSet (originCube d m) ∨
                      (∃ i : Fin d,
                        (MeetsUpperFace x m (n - 2) i ∨
                          MeetsLowerFace x m (n - 2) i) ∧
                        MemLp v.toFun 2 (volume.restrict (truncatedWindow x m n)) ∧
                        MemLp v.toFun 2
                          (volume.restrict (reflectedWindow x m (n - 2))) ∧
                        (∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
                          ∀ y ∈ reflectedWindow x m (n - 2),
                            v.toFun (coordFaceReflection
                              ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v.toFun y) ∧
                        (∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
                          ∀ y ∈ reflectedWindow x m (n - 2),
                            v.toFun (coordFaceReflection
                              (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -v.toFun y) ∧
                        HarmonicOnNhd
                          (v.toFun ∘
                            (Schauder.toEuc.symm :
                              EuclideanSpace ℝ (Fin d) → Vec d))
                          ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
                            reflectedWindow x m (n - 2)))) →
                    ∀ k : ℕ, 3 ≤ k →
                      affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun ≤
                        taylorContractionConst d * max (schauderWindowConst d) Cb
                            * windowRatioConst d 2
                            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
                            * affineExcess (truncatedWindow x m n) u.toFun
                          + triangleRemainderConst d
                              (max (schauderWindowConst d) Cb) k
                            * ((3 : ℝ) ^ (-n) *
                              (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
                                (C * Real.rpow s (-(4 : ℝ)) *
                                    fluxCorrectedErrorRepresentative M L (n - 2 + 3)
                                      ⟨s / 8, by linarith only [hs]⟩
                                      (Cutoff.translateCutoffSample z omega) *
                                    ((MeasureTheory.eLpNorm
                                        (fun y => u.toFun y -
                                          Homogenization.volumeAverage
                                            (((fun y' => z + y') ''
                                                openCubeSet
                                                  (originCube d (n - 2 + 3))) ∩
                                              openCubeSet (originCube d m))
                                            u.toFun) 2
                                        (normalizedVolumeMeasureOn
                                          (((fun y' => z + y') ''
                                              openCubeSet
                                                (originCube d (n - 2 + 3))) ∩
                                            openCubeSet
                                              (originCube d m)))).toReal +
                                      Real.rpow s (-(3 / 2 : ℝ)) *
                                          Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                                        ‖Homogenization.volumeAverageVec
                                            (((fun y' => z + y') ''
                                                openCubeSet
                                                  (originCube d (n - 2 + 2))) ∩
                                              openCubeSet (originCube d m))
                                            hdat.grad‖) +
                                  C * Real.rpow s (-(7 : ℝ)) *
                                      (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
                                      Real.rpow (3 : ℝ)
                                        ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                                    (normalizedGagliardoESeminormOn
                                      (((fun y' => z + y') ''
                                          openCubeSet
                                            (originCube d (n - 2 + 3))) ∩
                                        openCubeSet (originCube d m)) s g).toReal +
                                  C * Real.rpow s (-(6 : ℝ)) *
                                      Real.rpow (3 : ℝ)
                                        ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                                    (normalizedGagliardoESeminormOn
                                      (((fun y' => z + y') ''
                                          openCubeSet
                                            (originCube d (n - 2 + 3))) ∩
                                        openCubeSet (originCube d m)) s
                                      hdat.grad).toReal +
                                  C * Real.rpow s (-(6 : ℝ)) *
                                      Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                                    (MeasureTheory.eLpNorm hdat.grad 2
                                      (normalizedVolumeMeasureOn
                                        (((fun y' => z + y') ''
                                            openCubeSet
                                              (originCube d (n - 2 + 3))) ∩
                                          openCubeSet
                                            (originCube d m)))).toReal))) := by
  classical
  obtain ⟨Cb, hCb, hbd⟩ := excessDecay_oneStep_boundary_metSet_of_harmonicApprox_regated d hd
  obtain ⟨C, hC, hanchor⟩ := exists_oneStepAnchorBound d
  refine ⟨C, Cb, hC, hCb, ?_⟩
  intro M s hsrange hregime hfund hs delta hdelta1 hprice L m n hmL hnm x z hxz hz
  have hs1 : s ≤ 1 := hsrange.2
  have hxm : x ∈ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain z m (n - 3) hxz
  have hnm1 : n - 1 ≤ m := by omega
  have hnm2 : n - 2 ≤ m := by omega
  have hmn : n - 2 < m := by omega
  have hrep : s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) :=
    excessDecayDelta_repriced hC hs.le hprice
  have hmovsub : (fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)) ⊆ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet x hnm2
  filter_upwards [hanchor M s hsrange hregime hfund hs L m n hmL hnm x z hxz hz]
    with omega ha
  intro hmem u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv hwin k hk
  have hE0 : (0 : ℝ) ≤ affineExcess (truncatedWindow x m n) u.toFun :=
    affineExcess_nonneg _ _
  obtain ⟨B, hB, hharm, hexp⟩ := ha u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  have hR := ENNReal.toReal_nonneg.trans hexp
  have hu : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_domain x m n) le_rfl)
  rcases hwin with hcube | ⟨i, hmet, hv, hvR, hupv, hlowv, hharmclass⟩
  · have hmain := excessDecay_oneStep_interior_of_weaklyHarmonic_regated hd hk hs hs1 hdelta1 hxm hnm1
      hcube hu hharmv hmem hB hrep hharm
    refine oneStepConclusion_mono d (le_max_left _ _) hE0 hR ?_
    refine (by simpa only [mul_zero, add_zero] using hmain : _ ≤ _).trans ?_
    exact add_le_add le_rfl
      (oneStepRemainder_mono d (schauderWindowConst_nonneg d) k n hexp)
  · have huv : MemLp (fun y => u.toFun y - v.toFun y) 2
        (volume.restrict (movedReplacementCube x m n)) := by
      rw [movedReplacementCube]
      exact (u.memL2.mono_measure
        (Measure.restrict_mono hmovsub le_rfl)).sub v.memL2
    have hmain := hbd hk hs hs1 hdelta1 hxm hnm1 hmn hmet hu hv hvR huv hupv hlowv
      hharmclass hmem hB hrep hharm
    exact oneStepConclusion_mono d (le_max_right _ _) hE0 hR
      (hmain.trans (add_le_add le_rfl (oneStepRemainder_mono d hCb k n hexp)))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
