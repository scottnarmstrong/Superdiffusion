/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.AssemblyComposed
import Algsuperdiff.Section4.Provider.ExcessDecay.ReindexSlot

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Homogenization Homogenization.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-- Everything else is discharged from the proved chain: the boundary
Caccioppoli, the scaled parent-`L²` pricing, the composed datum pricing and the
two Dirichlet-energy legs at the coarse caps, the envelope, the `σ̄`-frame
division and the `σ̄` gap-3 conversion.  The frontier condition is never used,
so the display holds at every `z`; the gate binder is carried only to match the
frozen shape. -/
theorem hbdryOfScalarCoarse (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ openCubeSet (originCube d m) →
            z ∈ openCubeSet (originCube d m) →
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
              ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                openCubeSet (originCube d m) →
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
                  frontier (openCubeSet (originCube d m)) ≠ ∅)) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u h g →
                  MemLp g 2 (Support.normalizedVolumeMeasureOn
                    (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 h.grad) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  ∀ S : ℝ,
                  |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - h.toFun y)| ≤ S →
                  ∀ (v : H1Function
                        ((fun y => x + y) '' openCubeSet (originCube d n)))
                    (w : H10Function
                        ((fun y => x + y) '' openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => x + y) '' openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                          (Support.normalizedVolumeMeasureOn
                            ((fun y => x + y) ''
                              openCubeSet (originCube d n)))).toReal ≤
                        C *
                          (Real.rpow s (-(4 : ℝ)) *
                                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                  ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                ((eLpNorm
                                    (fun y =>
                                      u.toFun y -
                                        volumeAverage
                                          (((fun y' => z + y') ''
                                              openCubeSet (originCube d (n + 3))) ∩
                                            openCubeSet (originCube d m))
                                          u.toFun)
                                    2
                                    (Support.normalizedVolumeMeasureOn
                                      (((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 3))) ∩
                                        openCubeSet (originCube d m)))).toReal +
                                  Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                    ‖volumeAverageVec
                                        (((fun y' => z + y') ''
                                            openCubeSet (originCube d (n + 2))) ∩
                                          openCubeSet (originCube d m))
                                        h.grad‖) +
                            Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m)) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m)) s h.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                (eLpNorm h.grad 2
                                  (Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        openCubeSet (originCube d (n + 3))) ∩
                                      openCubeSet (originCube d m)))).toReal) +
                          C *
                            (Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) * S) := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd M.shellPrefix.dimension (by omega)
  haveI : NeZero d := ⟨hd⟩
  obtain ⟨CC, Cfin, hCC, hCfin, hcomp⟩ := exists_boundaryClauseComposed_honest d
  obtain ⟨CS, hCS, hS⟩ := exists_inv_sigmaBar_add_three_le d
  have hleC : CC ≤ max (max CC CS) (4 * Cfin) :=
    le_trans (le_max_left CC CS) (le_max_left _ _)
  have hleS : CS ≤ max (max CC CS) (4 * Cfin) :=
    le_trans (le_max_right CC CS) (le_max_left _ _)
  have hle4 : 4 * Cfin ≤ max (max CC CS) (4 * Cfin) := le_max_right _ _
  have hCpos : (0 : ℝ) < max (max CC CS) (4 * Cfin) := lt_of_lt_of_le hCC hleC
  have hle1 : Cfin ≤ max (max CC CS) (4 * Cfin) := by
    have h : Cfin ≤ 4 * Cfin := by linarith only [hCfin]
    linarith only [h, hle4]
  refine ⟨max (max CC CS) (4 * Cfin), hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx _hz hgeom _hgate
  have hregimeC : M.gamma ≤ CC⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCC hleC
    rw [one_div, one_div] at h1
    exact h1
  have hregimeS : M.gamma ≤ CS⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCS hleS
    rw [one_div, one_div] at h1
    exact h1
  have hsigconv := hS M hregimeS n
  filter_upwards [hcomp M s hsrange hregimeC hsmall hs L m n hmL hnm x z hx hgeom]
    with omega hom
  intro hmem u hdat g hsol hgL2 hgW hhW S hmean v w hharm hval hgrad
  have hreal := hom hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  have hErep0 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hS0 : (0 : ℝ) ≤ S := le_trans (abs_nonneg _) hmean
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  have hcompanion : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
      ‖volumeAverageVec
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m))) hdat.grad‖ :=
    mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _)
  refine hreal.trans (boundary_absorb ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCfin.le hle1 hle4)
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hcompanion)
      (mul_nonneg hS4 hErep0)
  · exact mul_nonneg (mul_nonneg hS4 hErep0)
      (add_nonneg ENNReal.toReal_nonneg hcompanion)
  · have hnn : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) *
        Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s g).toReal :=
      mul_nonneg (mul_nonneg hS7 h3sn) ENNReal.toReal_nonneg
    calc Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
          Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s g).toReal
        = (Real.rpow s (-(7 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) s g).toReal) *
          ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ := by ring
      _ ≤ (Real.rpow s (-(7 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) s g).toReal) *
            (4 * ((Annealed.sigmaBar M n : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left hsigconv hnn
      _ = 4 * (Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) s g).toReal) := by ring
  · exact mul_nonneg (mul_nonneg (mul_nonneg hS7 hsgn) h3sn) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg hS6 h3sn) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg hS6 h3n) ENNReal.toReal_nonneg
  · exact mul_nonneg (mul_nonneg hS4 hErep0) hS0


theorem hbdryOfScalarCoarse_constantS (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ openCubeSet (originCube d m) →
            z ∈ openCubeSet (originCube d m) →
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
              ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                openCubeSet (originCube d m) →
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
                  frontier (openCubeSet (originCube d m)) ≠ ∅)) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u h g →
                  MemLp g 2 (Support.normalizedVolumeMeasureOn
                    (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 h.grad) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  ∀ S : ℝ,
                  |volumeAverage ((fun y => wellPlacedCentre x m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - h.toFun y)| ≤ S →
                  ∀ (v : H1Function
                        ((fun y => x + y) '' openCubeSet (originCube d n)))
                    (w : H10Function
                        ((fun y => x + y) '' openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => x + y) '' openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                          (Support.normalizedVolumeMeasureOn
                            ((fun y => x + y) ''
                              openCubeSet (originCube d n)))).toReal ≤
                        C *
                          (Real.rpow s (-(4 : ℝ)) *
                                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                  ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                ((eLpNorm
                                    (fun y =>
                                      u.toFun y -
                                        volumeAverage
                                          (((fun y' => z + y') ''
                                              openCubeSet (originCube d (n + 3))) ∩
                                            openCubeSet (originCube d m))
                                          u.toFun)
                                    2
                                    (Support.normalizedVolumeMeasureOn
                                      (((fun y' => z + y') ''
                                          openCubeSet (originCube d (n + 3))) ∩
                                        openCubeSet (originCube d m)))).toReal +
                                  Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                    ‖volumeAverageVec
                                        (((fun y' => z + y') ''
                                            openCubeSet (originCube d (n + 2))) ∩
                                          openCubeSet (originCube d m))
                                        h.grad‖) +
                            Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m)) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m)) s h.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                (eLpNorm h.grad 2
                                  (Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        openCubeSet (originCube d (n + 3))) ∩
                                      openCubeSet (originCube d m)))).toReal) +
                          C * (Real.rpow s (-(4 : ℝ)) * S) := by
  classical
  obtain ⟨C1, hC1, hmainClause⟩ := hbdryOfScalarCoarse d
  obtain ⟨CE, hCE, hcap⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  have hle1 : C1 ≤ max (max C1 CE) (C1 * (CE * (1 / 2))) :=
    le_trans (le_max_left C1 CE) (le_max_left _ _)
  have hleE : CE ≤ max (max C1 CE) (C1 * (CE * (1 / 2))) :=
    le_trans (le_max_right C1 CE) (le_max_left _ _)
  have hleS : C1 * (CE * (1 / 2)) ≤ max (max C1 CE) (C1 * (CE * (1 / 2))) :=
    le_max_right _ _
  have hCpos : (0 : ℝ) < max (max C1 CE) (C1 * (CE * (1 / 2))) :=
    lt_of_lt_of_le hC1 hle1
  refine ⟨max (max C1 CE) (C1 * (CE * (1 / 2))), hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hz hgeom hgate
  have hregime1 : M.gamma ≤ C1⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (mul_le_mul_of_nonneg_right (inv_anti₀ hC1 hle1) (by positivity))
  have hregimeE : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    hregime.trans (mul_le_mul_of_nonneg_right (inv_anti₀ hCE hleE) (by positivity))
  filter_upwards [hmainClause M s hsrange hregime1 hsmall hs L m n hmL hnm x z hx hz
      hgeom hgate, hcap M s hsrange hregimeE hsmall hs n z] with omega hom hcapE
  intro hmem u hdat g hsol hgL2 hgW hhW S hmean v w hharm hval hgrad
  have hreal := hom hmem u hdat g hsol hgL2 hgW hhW S hmean v w hharm hval hgrad
  have hErepCap : Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) ≤
      CE * (1 / 2) := hcapE hmem L (le_trans hnm hmL)
  have hErep0 : (0 : ℝ) ≤ Support.fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hS0 : (0 : ℝ) ≤ S := le_trans (abs_nonneg _) hmean
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS7 : (0 : ℝ) ≤ Real.rpow s (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS6 : (0 : ℝ) ≤ Real.rpow s (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS32 : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3n : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (n : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  have hbracket : (0 : ℝ) ≤
      Real.rpow s (-(4 : ℝ)) *
          Support.fluxCorrectedErrorRepresentative M L (n + 3)
            ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
          ((eLpNorm (fun y => u.toFun y -
              volumeAverage ((((fun y' => z + y') ''
                  openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) u.toFun) 2
            (Support.normalizedVolumeMeasureOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))))).toReal +
            Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
              ‖volumeAverageVec
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
                  openCubeSet (originCube d m))) hdat.grad‖) +
        Real.rpow s (-(7 : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
            Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) s g).toReal +
        Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                openCubeSet (originCube d m))) s hdat.grad).toReal +
        Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
            (eLpNorm hdat.grad 2
              (Support.normalizedVolumeMeasureOn
                ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
                  openCubeSet (originCube d m))))).toReal :=
    add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hS4 hErep0)
        (add_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (mul_nonneg hS32 h3n) (norm_nonneg _))))
      (mul_nonneg (mul_nonneg (mul_nonneg hS7 hsgn) h3sn) ENNReal.toReal_nonneg))
      (mul_nonneg (mul_nonneg hS6 h3sn) ENNReal.toReal_nonneg))
      (mul_nonneg (mul_nonneg hS6 h3n) ENNReal.toReal_nonneg)
  have hleg : C1 * (Real.rpow s (-(4 : ℝ)) *
      Support.fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) * S) ≤
      (C1 * (CE * (1 / 2))) * (Real.rpow s (-(4 : ℝ)) * S) :=
    fluxWeighted_scalar_leg_le hC1.le hS4 hS0 hErepCap
  have hmainle := mul_le_mul_of_nonneg_right hle1 hbracket
  have hlegle : (C1 * (CE * (1 / 2))) * (Real.rpow s (-(4 : ℝ)) * S) ≤
      max (max C1 CE) (C1 * (CE * (1 / 2))) * (Real.rpow s (-(4 : ℝ)) * S) :=
    mul_le_mul_of_nonneg_right hleS (mul_nonneg hS4 hS0)
  linarith only [hreal, hleg, hmainle, hlegle]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
