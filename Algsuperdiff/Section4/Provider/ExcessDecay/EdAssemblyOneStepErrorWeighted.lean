/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyAnchorErrorWeighted
import Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyOneStep
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepInterior

/-!
# The anchored one-step at the error-weighted general clause

`EdAssemblyOneStep.excessDecay_oneStep_interior_anchored` discharges the
`hharm` slot of `OneStepInterior`'s siblings from the anchor and expands the
abstract `B.toReal` into the anchor's four printed legs.

This module is that theorem at the error-weighted general clause.

## The one moved leg, and the discard that is declined

`EdAssemblyAnchorErrorWeighted` delivers the anchor's expansion with the fourth leg

```text
   C s^{-6} · 𝓔_{n-2+3}(τ_z ω) · 3^{n-2} · ‖(∇h)_{(z+□_{n-2+2})∩□_m}‖ ,
```

the general clause's own flat `∇h` leg at the excess-decay lane's window
choice.  The `𝓔 1_𝒢 ≤ C(d) ε` step — the single monotone move that loses the
`𝓔` factor — is NOT taken here, exactly as it is declined throughout this
provider chain: the factor is carried into the display and spent downstream,
where `edLeg_four_le_errorWeighted` cashes it against the proved `𝓔 ≤ ε_j`.

## What is unchanged

Everything else.  The error weighting touches only the general clause's flat
`∇h` leg; in particular the gated indicator, the good event `𝒢(n-2+3, z; s/8,
C⁻¹ s⁴)`, the moved-cube carrier and the `δ` re-pricing `δ ≤ 64 C⁻² s⁶` are
untouched, so
`OneStepInterior.excessDecay_oneStep_interior_of_weaklyHarmonic_regated` (which is stated at
an abstract constant `Cv` in its `hrep`/`hharm` pair) applies verbatim, and
`oneStepRemainder_mono` does the substitution.  Nothing about the analysis of
the one-step changes; only the leg it reports.

## The `K_h` leg

The interior branch has **no** boundary-datum leg: the proved sibling's third
summand is `C_t (3^{n-k})^{1/2} · 0`, collapsed here, matching the printed
lemma's two `𝟙_{{(x+□_n)∩∂□_m ≠ ∅}}`-gated summands vanishing on the interior
branch.

## References

* ABK26, `l.excess.decay.good.scales`, statement and proof;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

/-- **The one-step excess-decay contraction off the anchor's general clause.**

`EdAssemblyOneStep.excessDecay_oneStep_interior_anchored` re-run at the
error-weighted statement: no `hharm` hypothesis, and the anchor's right-hand
side appears expanded into the four printed legs — the fourth of them the
`𝓔`-multiplied flat `∇h` average, at the anchor's own subterms.  This is the
display `stepFourDecay_of_edOneStepErrorWeighted` consumes. -/
theorem excessDecay_oneStep_interior_anchored_errorWeighted (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
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
            (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
              openCubeSet (originCube d m) →
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
                    ∀ k : ℕ, 3 ≤ k →
                      affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun ≤
                        taylorContractionConst d * schauderWindowConst d
                            * windowRatioConst d 2
                            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
                            * affineExcess (truncatedWindow x m n) u.toFun
                          + triangleRemainderConst d (schauderWindowConst d) k
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
                                      fluxCorrectedErrorRepresentative M L (n - 2 + 3)
                                        ⟨s / 8, by linarith only [hs]⟩
                                        (Cutoff.translateCutoffSample z omega) *
                                      Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                                    ‖Homogenization.volumeAverageVec
                                        (((fun y' => z + y') ''
                                            openCubeSet
                                              (originCube d (n - 2 + 2))) ∩
                                          openCubeSet (originCube d m))
                                        hdat.grad‖))) := by
  classical
  obtain ⟨C, hC, hanchor⟩ := exists_oneStepAnchorBound_errorWeighted d
  refine ⟨C, hC, ?_⟩
  intro M s hsrange hregime hfund hs delta hdelta1 hprice L m n hmL hnm x z hxz hz hcube
  have hs1 : s ≤ 1 := hsrange.2
  have hxm : x ∈ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain z m (n - 3) hxz
  have hnm1 : n - 1 ≤ m := by omega
  have hrep : s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) :=
    excessDecayDelta_repriced hC hs.le hprice
  filter_upwards [hanchor M s hsrange hregime hfund hs L m n hmL hnm x z hxz hz]
    with omega hom
  intro hmem u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv k hk
  obtain ⟨B, hB, hharm, hexp⟩ := hom u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  have hu : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_domain x m n) le_rfl)
  have hmain := excessDecay_oneStep_interior_of_weaklyHarmonic_regated hd hk hs hs1 hdelta1 hxm hnm1
    hcube hu hharmv hmem hB hrep hharm
  have hmain' := (by simpa only [mul_zero, add_zero] using hmain :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun ≤
      taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
          * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
          * affineExcess (truncatedWindow x m n) u.toFun
        + triangleRemainderConst d (schauderWindowConst d) k
          * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal)))
  exact hmain'.trans
    (add_le_add le_rfl (oneStepRemainder_mono d (schauderWindowConst_nonneg d) k n hexp))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
