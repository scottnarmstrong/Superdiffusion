/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBWellPlacedEndpoint

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

/-! ## 1. The degenerate zero-dimensional energy -/

/-- In dimension zero `vecNormSq` is the empty sum, so every `L²` norm of the
scalar gradient length vanishes. -/
private theorem eLpNorm_sqrt_vecNormSq_zeroDim (f : Vec 0 → Vec 0)
    (mu : Measure (Vec 0)) :
    eLpNorm (fun y => Real.sqrt (vecNormSq (f y))) 2 mu = 0 := by
  have hfun : (fun y => Real.sqrt (vecNormSq (f y))) = (fun _ : Vec 0 => (0 : ℝ)) := by
    funext y
    simp [vecNormSq, vecDot]
  rw [hfun]
  simp

/-! ## 2. The endpoint at every dimension -/

theorem anomalous_regularity_provider_final (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
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
                ∀ (u h : Homogenization.H1Function
                      (Homogenization.openCubeSet (Homogenization.originCube d m)))
                  (g : Homogenization.Vec d → Homogenization.Vec d)
                  (Kg Kh : ℝ),
                  Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (Homogenization.originCube d m) u h g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kg g →
                  Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      (1 / 2) Kh h.grad →
                  (∀ y ∈ Homogenization.openCubeSet (Homogenization.originCube d m),
                    ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                  Algsuperdiff.Section4.Support.HasGradientOn
                      (Homogenization.openCubeSet (Homogenization.originCube d m))
                      h.toFun h.grad →
                  ∀ x : Homogenization.Vec d,
                    x ∈ Homogenization.openCubeSet (Homogenization.originCube d m) →
                    ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                      (ENNReal.ofReal (Real.sqrt M.nu) *
                          MeasureTheory.eLpNorm
                            (fun y => Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y => x + y) ''
                                  Homogenization.openCubeSet (Homogenization.originCube d n)) ∩
                                Homogenization.openCubeSet (Homogenization.originCube d m))) ≤
                        ENNReal.ofReal
                            (C *
                              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          (ENNReal.ofReal (Real.sqrt M.nu) *
                              MeasureTheory.eLpNorm
                                (fun y =>
                                  Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                                (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                  (Homogenization.openCubeSet
                                    (Homogenization.originCube d m))) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                      (x ∈ Homogenization.openCubeSet (Homogenization.originCube d (m - 1)) →
                        ENNReal.ofReal (Real.sqrt M.nu) *
                            MeasureTheory.eLpNorm
                              (fun y => Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                (((fun y => x + y) ''
                                    Homogenization.openCubeSet
                                      (Homogenization.originCube d n)) ∩
                                  Homogenization.openCubeSet (Homogenization.originCube d m))) ≤
                          ENNReal.ofReal
                              (C *
                                Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                            (ENNReal.ofReal (Real.sqrt M.nu) *
                                MeasureTheory.eLpNorm
                                  (fun y =>
                                    Real.sqrt (Homogenization.vecNormSq (u.grad y))) 2
                                  (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                    (Homogenization.openCubeSet
                                      (Homogenization.originCube d m))) +
                              ENNReal.ofReal
                                (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)))
    := by
  rcases eq_or_ne d 0 with hd0 | hd0
  · subst hd0
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma0 alpha _ha0 _ha m
    refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
    · intro N
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        refine le_trans prob_le_one (ENNReal.one_le_ofReal.mpr ?_)
        rw [one_mul]
        refine Real.one_le_exp (div_nonneg ?_ ?_)
        · have hsq : (0 : ℝ) ≤ (1 - alpha) ^ (2 : ℕ) := sq_nonneg (1 - alpha)
          push_cast
          linarith only [hsq]
        · have hgam : 0 < M.gamma := M.shellPrefix.gamma_pos
          linarith only [hgam]
      · have hnull :
            (Cutoff.cutoffSampleLaw M).toMeasure
              {omega : Cutoff.CutoffSample 0 | (N : ℕ∞) ≤ (0 : ℕ∞)} = 0 := by
          have hset : {omega : Cutoff.CutoffSample 0 | (N : ℕ∞) ≤ (0 : ℕ∞)} = ∅ := by
            ext omega
            simp [hN.ne']
          rw [hset, measure_empty]
        exact le_trans (le_of_eq hnull) (zero_le _)
    · refine Filter.Eventually.of_forall ?_
      intro _omega _L _hL u _h _g Kg Kh _hdir _hKg _hKh _hsup _hgradh x _hx n _hn _hpay
      have hzero : ∀ mu : Measure (Vec 0),
          eLpNorm (fun y => Real.sqrt (vecNormSq (u.grad y))) 2 mu = 0 :=
        fun mu => eLpNorm_sqrt_vecNormSq_zeroDim u.grad mu
      refine ⟨?_, ?_⟩
      · simp only [hzero, mul_zero]
        exact zero_le _
      · intro _hxm
        simp only [hzero, mul_zero]
        exact zero_le _
  · haveI : NeZero d := ⟨hd0⟩
    exact anomalous_regularity_provider_wellPlaced d hd0 cstar 1 hcstar one_pos

end

end Algsuperdiff.Section4.Provider.Regularity
