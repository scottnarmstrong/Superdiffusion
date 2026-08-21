/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyAnchor
import Algsuperdiff.Section4.Provider.ExcessDecay.OneStepInterior

/-!
# The interior one-step contraction, unconditional on the anchor

The `hharm` slot of `OneStepInterior`'s `_regated` siblings is **discharged**
here from the anchor (`EdAssemblyAnchor.exists_oneStepAnchorBound`), and the
abstract `B.toReal` of the proved display is **expanded** into the anchor's
four printed legs.  What remains is a one-step excess-decay contraction with no
harmonic-approximation hypothesis at all: for every `ω` of the development's
own good-scale supply event `𝒢(n-2+3, z; s/8, (s/8)√δ)`, at the re-priced `δ ≤
64 C⁻² s⁶`, the contraction holds outright.

## The two moves, and why they are free

* **Reachability.**  The supply threshold `(s/8)√δ` sits below the frozen
  threshold `C⁻¹ s⁴` exactly at the price
  `δ ≤ 64 C⁻² s⁶` (`RebaseEpsilon.excessDecayDelta_repriced`); at the `s = 1/4`
  pin of the sole eventual consumer this is the constant `C⁻²/64`, so the
  `γ`-exponent and the `1 − C γ^{1/2}` target are untouched.
* **Expansion.**  `EdAssemblyLegs.toReal_ofReal_mul_bracket_add_three_le`, then
  monotonicity of the remainder slot in `B.toReal`.  The remainder constant
  `triangleRemainderConst` is nonnegative, so the substitution is a single
  `add_le_add`.

## The `K_h` leg

The interior branch has **no** boundary-datum leg: the proved sibling's third
summand is `C_t (3^{n-k})^{1/2} · 0`, collapsed here.  That matches the printed
lemma, whose two `𝟙_{{(x+□_n)∩∂□_m ≠ ∅}}`-gated summands vanish on the interior
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

/-! ## 1. The two abstract-real moves of the one-step conclusion -/

/-- **Monotonicity of the one-step remainder slot.**  The remainder is
`C_r(d,C,k) · 3^{-n} · √((3²)^d) · R`, increasing in `R` because
`triangleRemainderConst` is nonnegative. -/
theorem oneStepRemainder_mono (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (n : ℤ)
    {R R' : ℝ} (hRR' : R ≤ R') :
    triangleRemainderConst d C k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R)) ≤
      triangleRemainderConst d C k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R')) :=
  mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hRR' (Real.sqrt_nonneg _))
      (zpow_pos (by norm_num) (-n)).le)
    (triangleRemainderConst_nonneg d hC k)

/-- **Monotonicity of the whole one-step conclusion in the Schauder constant.**
Used by the interior/boundary join to raise both branches to one constant. -/
theorem oneStepConclusion_mono (d : ℕ) {C C' : ℝ} (hCC' : C ≤ C')
    {k : ℕ} {n : ℤ} {Ek E0 R : ℝ} (hE0 : 0 ≤ E0) (hR : 0 ≤ R)
    (h : Ek ≤ taylorContractionConst d * C * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0
          + triangleRemainderConst d C k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R))) :
    Ek ≤ taylorContractionConst d * C' * windowRatioConst d 2
          * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0
        + triangleRemainderConst d C' k
          * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R)) := by
  have hcontr : taylorContractionConst d * C * windowRatioConst d 2
        * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0 ≤
      taylorContractionConst d * C' * windowRatioConst d 2
        * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E0 := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ (windowRatioConst_nonneg d 2))
      (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)) hE0
    exact mul_le_mul_of_nonneg_left hCC' (taylorContractionConst_nonneg d)
  have hrem : triangleRemainderConst d C k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R)) ≤
      triangleRemainderConst d C' k
        * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * R)) := by
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (zpow_pos (by norm_num) (-n)).le
        (mul_nonneg (Real.sqrt_nonneg _) hR))
    rw [triangleRemainderConst, triangleRemainderConst]
    have := mul_le_mul_of_nonneg_left hCC'
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) (taylorContractionConst_nonneg d))
    linarith only [this]
  exact h.trans (add_le_add hcontr hrem)

/-! ## 2. The composed interior one-step -/

/-- **The interior one-step excess-decay contraction, off the anchor.**

No `hharm` hypothesis: the harmonic-approximation display is *applied*, and its
right-hand side appears expanded into the four printed legs. -/
theorem excessDecay_oneStep_interior_anchored (d : ℕ) [NeZero d] (hd : d ≠ 0) :
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
                                      Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                                    (MeasureTheory.eLpNorm hdat.grad 2
                                      (normalizedVolumeMeasureOn
                                        (((fun y' => z + y') ''
                                            openCubeSet
                                              (originCube d (n - 2 + 3))) ∩
                                          openCubeSet
                                            (originCube d m)))).toReal))) := by
  classical
  obtain ⟨C, hC, hanchor⟩ := exists_oneStepAnchorBound d
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
