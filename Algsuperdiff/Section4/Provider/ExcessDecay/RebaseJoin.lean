/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.Join
import Algsuperdiff.Section4.Provider.ExcessDecay.RebaseWeakening

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 1. The joint-constant absorption, on abstract reals -/

/-- Raising a four-summand right-hand side from the caller's constant to the joint
constant of the assembly. -/
private theorem four_summand_absorb {C₀ C t₁ t₂ t₃ t₄ : ℝ} (h : C₀ ≤ C)
    (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) (h₄ : 0 ≤ t₄) :
    C₀ * (t₁ + t₂ + t₃ + t₄) ≤ C * t₁ + C * t₂ + C * t₃ + C * t₄ := by
  have e₁ := mul_le_mul_of_nonneg_right h h₁
  have e₂ := mul_le_mul_of_nonneg_right h h₂
  have e₃ := mul_le_mul_of_nonneg_right h h₃
  have e₄ := mul_le_mul_of_nonneg_right h h₄
  have hexp : C₀ * (t₁ + t₂ + t₃ + t₄) =
      C₀ * t₁ + C₀ * t₂ + C₀ * t₃ + C₀ * t₄ := by ring
  rw [hexp]
  linarith only [e₁, e₂, e₃, e₄]

/-! ## 2. The conditional provider assembly at the moved legs -/

/-- **The frozen block, from the proved interior chain and one real-valued
caller obligation.**

The conclusion is the frozen statement byte-for-byte (only the two
indicator binders `omega'` carry a leading underscore, forced by the
repository's zero-warning gate: the frozen file escapes the `unusedVariables`
linter only through its `sorry`).  The hypothesis `hgen` is a conditional A
obligation, not a premise of the pinned source statement. -/
theorem exists_harmonicApproximation_provider_of_generalClauseReal_legMoved (d : ℕ)
    (hgen : ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : Homogenization.Vec d,
            x ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
            z ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
            (fun y => x + y) '' Homogenization.openCubeSet (Homogenization.originCube d n) ⊆
              ((fun y => z + y) ''
                  Homogenization.openCubeSet (Homogenization.originCube d (n + 1))) ∩
                Homogenization.openCubeSet (Homogenization.originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                ∀ (u h : Homogenization.H1Function
                      (Homogenization.openCubeSet (Homogenization.originCube d m)))
                  (g : Homogenization.Vec d → Homogenization.Vec d),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (Homogenization.originCube d m) u h g →
                  MeasureTheory.MemLp g 2
                      (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                        (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                  MeasureTheory.MemLp (Homogenization.Gagliardo.gagliardoKernel s 2 g) 2
                      (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                        (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                  MeasureTheory.MemLp (Homogenization.Gagliardo.gagliardoKernel s 2 h.grad) 2
                      (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                        (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                  ∀ (v : Homogenization.H1Function
                        ((fun y => x + y) ''
                          Homogenization.openCubeSet (Homogenization.originCube d n)))
                    (w : Homogenization.H10Function
                        ((fun y => x + y) ''
                          Homogenization.openCubeSet (Homogenization.originCube d n))),
                    Algsuperdiff.Section4.Support.IsWeaklyHarmonicOn
                        ((fun y => x + y) ''
                          Homogenization.openCubeSet (Homogenization.originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                          (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                            ((fun y => x + y) ''
                              Homogenization.openCubeSet
                                (Homogenization.originCube d n)))).toReal ≤
                        C *
                          (Real.rpow s (-(4 : ℝ)) *
                                Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative
                                  M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
                                  (Cutoff.translateCutoffSample z omega) *
                                ((MeasureTheory.eLpNorm
                                    (fun y =>
                                      u.toFun y -
                                        Homogenization.volumeAverage
                                          (((fun y' => z + y') ''
                                              Homogenization.openCubeSet
                                                (Homogenization.originCube d (n + 3))) ∩
                                            Homogenization.openCubeSet
                                              (Homogenization.originCube d m))
                                          u.toFun)
                                    2
                                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                      (((fun y' => z + y') ''
                                          Homogenization.openCubeSet
                                            (Homogenization.originCube d (n + 3))) ∩
                                        Homogenization.openCubeSet
                                          (Homogenization.originCube d m)))).toReal +
                                  Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                    ‖Homogenization.volumeAverageVec
                                        (((fun y' => z + y') ''
                                            Homogenization.openCubeSet
                                              (Homogenization.originCube d (n + 2))) ∩
                                          Homogenization.openCubeSet
                                            (Homogenization.originCube d m))
                                        h.grad‖) +
                            Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 3))) ∩
                                    Homogenization.openCubeSet
                                      (Homogenization.originCube d m)) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                                (Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 3))) ∩
                                    Homogenization.openCubeSet
                                      (Homogenization.originCube d m)) s h.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
                                (MeasureTheory.eLpNorm h.grad 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (((fun y' => z + y') ''
                                        Homogenization.openCubeSet
                                          (Homogenization.originCube d (n + 3))) ∩
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d m)))).toReal)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m →
          ∀ x z : Homogenization.Vec d,
            x ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
            z ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
            (fun y => x + y) '' Homogenization.openCubeSet (Homogenization.originCube d n) ⊆
              ((fun y => z + y) ''
                  Homogenization.openCubeSet (Homogenization.originCube d (n + 1))) ∩
                Homogenization.openCubeSet (Homogenization.originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (u h : Homogenization.H1Function
                    (Homogenization.openCubeSet (Homogenization.originCube d m)))
                (g : Homogenization.Vec d → Homogenization.Vec d),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (Homogenization.originCube d m) u h g →
                MeasureTheory.MemLp g 2
                    (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                MeasureTheory.MemLp (Homogenization.Gagliardo.gagliardoKernel s 2 g) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                MeasureTheory.MemLp (Homogenization.Gagliardo.gagliardoKernel s 2 h.grad) 2
                    (Algsuperdiff.Section4.Support.normalizedGagliardoMeasureOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))) →
                ∀ (v : Homogenization.H1Function
                      ((fun y => x + y) ''
                        Homogenization.openCubeSet (Homogenization.originCube d n)))
                  (w : Homogenization.H10Function
                      ((fun y => x + y) ''
                        Homogenization.openCubeSet (Homogenization.originCube d n))),
                  Algsuperdiff.Section4.Support.IsWeaklyHarmonicOn
                      ((fun y => x + y) ''
                        Homogenization.openCubeSet (Homogenization.originCube d n)) v →
                  (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                  (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                  (Set.indicator
                        (Algsuperdiff.Frozen.Section4.goodEventAt M
                          (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 3) z
                          ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
                        (fun _omega' =>
                          MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              ((fun y => x + y) ''
                                Homogenization.openCubeSet (Homogenization.originCube d n))))
                        omega ≤
                      ENNReal.ofReal
                          (C * Real.rpow s (-(4 : ℝ)) *
                            Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                              (n + 3) ⟨s / 8, by linarith only [hs]⟩
                              (Cutoff.translateCutoffSample z omega)) *
                        (MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                Homogenization.volumeAverage
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 3))) ∩
                                    Homogenization.openCubeSet (Homogenization.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  Homogenization.openCubeSet
                                    (Homogenization.originCube d (n + 3))) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m))) +
                          ENNReal.ofReal
                            (Real.rpow s (-(3 / 2 : ℝ)) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              ‖Homogenization.volumeAverageVec
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 2))) ∩
                                    Homogenization.openCubeSet (Homogenization.originCube d m))
                                  h.grad‖)) +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(7 : ℝ)) *
                              (Annealed.sigmaBar M n : ℝ)⁻¹ *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                Homogenization.openCubeSet
                                  (Homogenization.originCube d (n + 3))) ∩
                              Homogenization.openCubeSet (Homogenization.originCube d m)) s g +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                          Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                Homogenization.openCubeSet
                                  (Homogenization.originCube d (n + 3))) ∩
                              Homogenization.openCubeSet (Homogenization.originCube d m)) s
                            h.grad +
                        ENNReal.ofReal
                            (C * Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ)) *
                          MeasureTheory.eLpNorm h.grad 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  Homogenization.openCubeSet
                                    (Homogenization.originCube d (n + 3))) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m)))) ∧
                    ((((fun y' => z + y') ''
                            Homogenization.openCubeSet
                              (Homogenization.originCube d (n + 2))) ∩
                          frontier
                            (Homogenization.openCubeSet (Homogenization.originCube d m)) =
                        ∅) →
                      Set.indicator
                          (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) (n + 2) z
                            ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
                          (fun _omega' =>
                            MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                ((fun y => x + y) ''
                                  Homogenization.openCubeSet (Homogenization.originCube d n))))
                          omega ≤
                        ENNReal.ofReal
                            (C * Real.rpow s (-(4 : ℝ)) *
                              Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
                                (n + 2) ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega)) *
                          MeasureTheory.eLpNorm
                            (fun y =>
                              u.toFun y -
                                Homogenization.volumeAverage
                                  (((fun y' => z + y') ''
                                      Homogenization.openCubeSet
                                        (Homogenization.originCube d (n + 2))) ∩
                                    Homogenization.openCubeSet (Homogenization.originCube d m))
                                  u.toFun)
                            2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y' => z + y') ''
                                  Homogenization.openCubeSet
                                    (Homogenization.originCube d (n + 2))) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m))) +
                          ENNReal.ofReal
                              (C * Real.rpow s (-(19 / 2 : ℝ)) *
                                (Annealed.sigmaBar M n : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ))) *
                            Algsuperdiff.Section4.Support.normalizedGagliardoESeminormOn
                              (((fun y' => z + y') ''
                                  Homogenization.openCubeSet
                                    (Homogenization.originCube d (n + 2))) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m)) s g)
    := by
  classical
  obtain ⟨CG, hCG, hG⟩ := hgen
  obtain ⟨CI, hCI, hI⟩ := exists_interiorClause_anchorShape d
  have hleG : CG ≤ max CG CI := le_max_left _ _
  have hleI : CI ≤ max CG CI := le_max_right _ _
  have hCpos : (0 : ℝ) < max CG CI := lt_of_lt_of_le hCG hleG
  refine ⟨max CG CI, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hx hz hgeom
  have hnm2 : n + 2 ≤ m := by omega
  have hregimeG : M.gamma ≤ CG⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCG hleG
    rw [one_div, one_div] at h1
    exact h1
  have hregimeI : M.gamma ≤ CI⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h1 := one_div_le_one_div_of_le hCI hleI
    rw [one_div, one_div] at h1
    exact h1
  filter_upwards [hG M s hsrange hregimeG hsmall hs L m n hmL hnm x z hx hz hgeom,
    hI M s hsrange hregimeI hsmall hs L m n hmL hnm2 x z hx hz hgeom] with omega hgen' hint'
  intro u hdat g hsol hgL2 hgW hhW v w hharm hval hgrad
  have hEr : (0 : ℝ) ≤ Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
      (n + 3) ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hEr2 : (0 : ℝ) ≤ Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative M L
      (n + 2) ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    Algsuperdiff.Section4.Support.fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hsg : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M n).2.le
  have hne : eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n))) ≠ ⊤ :=
    eLpNorm_ne_top_of_eq_h10 (volume_image_add_openCubeSet_ne_zero x (originCube d n)) w
      (fun y => by rw [hval y]; ring)
  refine ⟨?_, ?_⟩
  · refine indicator_le_of_mem ?_
    intro hmem
    have hreal := hgen' hmem u hdat g hsol hgL2 hgW hhW v w hharm hval hgrad
    have hb : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) (n : ℝ) *
        ‖Homogenization.volumeAverageVec
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2)))) ∩
              openCubeSet (originCube d m)) hdat.grad‖ :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg (by norm_num) _))
        (norm_nonneg _)
    refine le_ofReal_mul_bracket_add_three hne
      (mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hs.le _)) hEr) hb
      (mul_nonneg (mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hs.le _)) hsg)
        (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hs.le _))
        (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg hs.le _))
        (Real.rpow_nonneg (by norm_num) _)) ?_
    refine hreal.trans ?_
    refine le_trans (four_summand_absorb hleG ?_ ?_ ?_ ?_) (le_of_eq (by ring))
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) hEr)
        (add_nonneg ENNReal.toReal_nonneg hb)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) hsg)
        (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
        (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _)
        (Real.rpow_nonneg (by norm_num) _)) ENNReal.toReal_nonneg
  · intro hgate
    refine le_trans (hint' u hdat g hsol hgL2 hgW hhW v w hharm hval hgrad hgate) ?_
    refine two_summand_coeff_mono ?_ ?_
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hleI (Real.rpow_nonneg hs.le _)) hEr2
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hleI (Real.rpow_nonneg hs.le _)) hsg)
        (Real.rpow_nonneg (by norm_num) _)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
