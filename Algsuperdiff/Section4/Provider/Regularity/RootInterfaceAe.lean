/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootAssemblyConditional

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The a.e. sibling of the lattice display -/

/-- **`e.energy.density.estimate` at the lattice centre, almost surely.**

The body is `RootAssemblyConditional.RootLatticeDisplay`'s, character for
character; the only change is the position of the `ω` quantifier, which is `∀ᵐ
ω` here and sits inside `∀ m` and outside `∀ n`, exactly as the clause-(B)
endpoint `rootClauseB_display_offGrid_final` produces it.  This is the shape
every §4.4 producer of the display can actually deliver: the good-event supply
is probabilistic.

`RootLatticeDisplayAe_of_forall` shows it is implied by the `∀ ω` version. -/
def RootLatticeDisplayAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
  ∀ m : ℤ,
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ n : ℤ, n ≤ m →
        RootWindowPayload M C1 alpha n m omega →
          ∀ L : ℤ, m ≤ L →
            ∀ (u h : H1Function (openCubeSet (originCube d m)))
              (g : Vec d → Vec d) (Kg Kh : ℝ),
              Support.IsDirichletSolutionOn
                  (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                  (originCube d m) u h g →
              Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                  (1 / 2) Kg g →
              Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                  (1 / 2) Kh h.grad →
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (Real.sqrt M.nu *
                    Support.normalizedL2On
                      (truncatedWindow (offGridCentre n x) m (n + 1))
                      (fun y => Real.sqrt (vecNormSq (u.grad y)))
                  ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                    (Real.sqrt M.nu *
                        Support.normalizedL2On (openCubeSet (originCube d m))
                          (fun y => Real.sqrt (vecNormSq (u.grad y)))
                      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
                      + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ∧
                  (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
                    Real.sqrt M.nu *
                        Support.normalizedL2On
                          (truncatedWindow (offGridCentre n x) m (n + 1))
                          (fun y => Real.sqrt (vecNormSq (u.grad y)))
                      ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                        (Real.sqrt M.nu *
                            Support.normalizedL2On (openCubeSet (originCube d m))
                              (fun y => Real.sqrt (vecNormSq (u.grad y)))
                          + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                              Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg))

/-- **The a.e. display is a weakening of the `∀ ω` display.**  One direction only:
the reverse is false, which is precisely why the re-cut is needed. -/
theorem RootLatticeDisplayAe_of_forall {M : ABKModel d} {C1 Cest alpha : ℝ}
    (h : RootLatticeDisplay M C1 Cest alpha) :
    RootLatticeDisplayAe M C1 Cest alpha := fun m =>
  Filter.Eventually.of_forall fun omega n hn hpay L hL u hdat g Kg Kh hdir hKg hKh =>
    h n m hn omega hpay L hL u hdat g Kg Kh hdir hKg hKh

/-! ## 2. The root provider from the a.e. display -/

/-- **`t.regularity`, conditional on the §4.4 a.e. lattice display.**

The frozen root's entire conclusion — including the sup binder
`∀ y ∈ □_m, ‖∇h(y)‖ ≤ 3^{m/2} K_h`, which is introduced and immediately
discharged — produced from `hdisplay` and the proved §4.4 outer chain.

The produced constant is `C = max C₀ (3^d·C_est)`: `C₀` is the minimal-scale
constant/ (which serves the tail and the `α`-range) and `3^d·C_est` is the
estimate's constant after's off-grid transfer; the maximum is legitimate
because every role of `C` in the printed statement is monotone-weakening in `C`
(`RootAssemblyParameters` §3).

`C_edos` is the abstract excess-decay one-step constant, `C_iter` the abstract
Step-6 iteration constant, `C_ann` the annular constant naming `C₁`; all three
are the node's own, and `hdisplay` is stated at the `C₁` they determine
together with the Step-1 index `k ≥ 11`.

The a.e. re-cut costs exactly one extra `filter_upwards` argument: `m` is fixed
before the `∃ X`, so no quantifier move over `n` and no countable-union
argument is performed. -/
theorem anomalous_regularity_provider_of_latticeDisplayAe (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) (Cedos Citer Cann Cest : ℝ) (k : ℕ) (hk : 11 ≤ k)
    (hCest : 0 ≤ Cest)
    (hdisplay : ∀ (M : ABKModel d) (alpha : ℝ),
      RootLatticeDisplayAe M (stepOneC1 d Cedos Cann Citer k) Cest alpha) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Cutoff.CutoffSample d → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ L : ℤ, m ≤ L →
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d) (Kg Kh : ℝ),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u h g →
                  Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                      (1 / 2) Kg g →
                  Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ y ∈ openCubeSet (originCube d m),
                    ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                  ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                    ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                      (ENNReal.ofReal (Real.sqrt M.nu) *
                          eLpNorm
                            (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                            (Support.normalizedVolumeMeasureOn
                              (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
                                openCubeSet (originCube d m))) ≤
                        ENNReal.ofReal
                            (C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          (ENNReal.ofReal (Real.sqrt M.nu) *
                              eLpNorm
                                (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                                (Support.normalizedVolumeMeasureOn
                                  (openCubeSet (originCube d m))) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                      (x ∈ openCubeSet (originCube d (m - 1)) →
                        ENNReal.ofReal (Real.sqrt M.nu) *
                            eLpNorm
                              (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                              (Support.normalizedVolumeMeasureOn
                                (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
                                  openCubeSet (originCube d m))) ≤
                          ENNReal.ofReal
                              (C *
                                Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                            (ENNReal.ofReal (Real.sqrt M.nu) *
                                eLpNorm
                                  (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                                  (Support.normalizedVolumeMeasureOn
                                    (openCubeSet (originCube d m))) +
                              ENNReal.ofReal
                                (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg))) := by
  obtain ⟨gamma0, C0, hg0pos, hC0pos, _, _, _, hpkg⟩ :=
    rootAssembly_aePackage d cstar hcstar Cedos Citer Cann k hk
  refine ⟨gamma0, max C0 ((3 : ℝ) ^ d * Cest), hg0pos,
    lt_of_lt_of_le hC0pos (le_max_left _ _), ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have halphaC0 : alpha ≤ 1 - C0 * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_max_left _ _) halpha
  obtain ⟨Z, hXmeas, hXtail, hae⟩ := hpkg M hcs hgamma alpha halpha0 halphaC0 m
  refine ⟨minimalScaleX Z k, hXmeas, ?_, ?_⟩
  · intro N
    exact le_trans (hXtail N)
      (minimalScaleTail_ofReal_mono_const hC0pos (le_max_left _ _) hgpos)
  filter_upwards [hae, hdisplay M alpha m] with omega hpay hdisp
  intro L hL u h g Kg Kh hdir hKg hKh _hsup x hx n hn hgate
  have hzform := hdisp n hn (hpay n hn hgate) L hL u h g Kg Kh hdir hKg hKh x hx
  have hpair := rootEnergyDensityPair_of_realDisplays M.nu
    (fun y => Real.sqrt (vecNormSq (u.grad y))) hx hn hCest
    (memLp_two_sqrt_vecNormSq_grad u) hzform.1 hzform.2
  have hCle : ((3 : ℝ) ^ d * Cest) *
      Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) ≤
      max C0 ((3 : ℝ) ^ d * Cest) *
        Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcoef : ENNReal.ofReal
        (((3 : ℝ) ^ d * Cest) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) ≤
      ENNReal.ofReal
        (max C0 ((3 : ℝ) ^ d * Cest) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) :=
    ENNReal.ofReal_le_ofReal hCle
  refine ⟨le_trans hpair.1 (mul_le_mul' hcoef (le_refl _)), fun hxin => ?_⟩
  exact le_trans (hpair.2 hxin) (mul_le_mul' hcoef (le_refl _))

end

end Algsuperdiff.Section4.Provider.Regularity
