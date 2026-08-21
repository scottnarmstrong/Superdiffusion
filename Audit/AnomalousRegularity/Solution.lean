import Mathlib
import Algsuperdiff.MainTheorems
import Audit.AnomalousRegularity.SolutionBasic
import Audit.Support.AnomalousRegularityBridge

/-!
# Solution: AnomalousRegularity

The challenge module `Audit/AnomalousRegularity/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `Audit.AnomalousRegularity.SolutionBasic` — a verbatim copy of the
challenge's statement vocabulary — and proves the audited theorem with a
byte-identical statement, through the bridges in `Audit/Support/`.
-/

namespace Algsuperdiff
namespace StatementAudit
namespace AnomalousRegularity

open Audit.Support.ARBridge
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

theorem anomalous_regularity
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : Model d, RealizesCstar d M.P cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ,
            ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
              |sigmaBarM -
                  Real.sqrt (M.nu ^ (2 : ℕ) +
                    cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
                C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
            ∃ X : CutoffSample d → ℕ∞,
              Measurable X ∧
              (∀ N : ℕ,
                  cutoffSampleMeasure M.P {omega | (N : ℕ∞) ≤ X omega} ≤
                    ENNReal.ofReal
                      (C * Real.exp
                        (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
              ∀ᵐ omega ∂cutoffSampleMeasure M.P,
                ∀ L : ℤ, m ≤ L →
                  ∀ (u h : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d)
                    (Kg Kh : ℝ),
                    IsDirichletSolutionOn (coefficientCutoff M.nu L omega)
                      (originCube d m) u h g →
                    HolderSeminormBoundOn (openCubeSet (originCube d m))
                      (1 / 2) Kg g →
                    HolderSeminormBoundOn (openCubeSet (originCube d m))
                      (1 / 2) Kh h.grad →
                    (∀ y ∈ openCubeSet (originCube d m),
                      ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                    HasGradientOn (openCubeSet (originCube d m))
                      h.toFun h.grad →
                    ∀ x : Vec d,
                      x ∈ openCubeSet (originCube d m) →
                      ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                        (ENNReal.ofReal (Real.sqrt M.nu) *
                            eLpNorm
                              (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                              (normalizedVolumeMeasureOn
                                (((fun y => x + y) ''
                                    openCubeSet (originCube d n)) ∩
                                  openCubeSet (originCube d m))) ≤
                          ENNReal.ofReal
                              (C *
                                Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                            (ENNReal.ofReal (Real.sqrt M.nu) *
                                eLpNorm
                                  (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                                  (normalizedVolumeMeasureOn
                                    (openCubeSet (originCube d m))) +
                              ENNReal.ofReal
                                (Real.sqrt sigmaBarM⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                              ENNReal.ofReal
                                (Real.sqrt sigmaBarM *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                        (x ∈ openCubeSet (originCube d (m - 1)) →
                          ENNReal.ofReal (Real.sqrt M.nu) *
                              eLpNorm
                                (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                                (normalizedVolumeMeasureOn
                                  (((fun y => x + y) ''
                                      openCubeSet (originCube d n)) ∩
                                    openCubeSet (originCube d m))) ≤
                            ENNReal.ofReal
                                (C *
                                  Real.rpow (3 : ℝ)
                                    ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                              (ENNReal.ofReal (Real.sqrt M.nu) *
                                  eLpNorm
                                    (fun y => Real.sqrt (vecNormSq (u.grad y))) 2
                                    (normalizedVolumeMeasureOn
                                      (openCubeSet (originCube d m))) +
                                ENNReal.ofReal
                                  (Real.sqrt sigmaBarM⁻¹ *
                                      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg))) := by
  obtain ⟨g0, C0, hg0, hC0, hmain⟩ :=
    _root_.Algsuperdiff.anomalous_regularity d cstar _hcstar
  obtain ⟨Cib, hCib, hbandAll⟩ := exists_sigmaBar_profile_band d
  set Cmax : ℝ := max C0 (Cib * cstar⁻¹ ^ 2) with hCmaxdef
  have hCmaxpos : 0 < Cmax := lt_of_lt_of_le hC0 (le_max_left _ _)
  have hC0le : C0 ≤ Cmax := le_max_left _ _
  have hCible : Cib * cstar⁻¹ ^ 2 ≤ Cmax := le_max_right _ _
  have hg0b : (0 : ℝ) < (Cib⁻¹) ^ 10 * cstar ^ 10 := by positivity
  refine ⟨min g0 ((Cib⁻¹) ^ 10 * cstar ^ 10), Cmax, lt_min hg0 hg0b, hCmaxpos, ?_⟩
  intro M hreal hgamma alpha halpha0 halpha m
  have hcs : _root_.Algsuperdiff.Section3.Disorder.cstar (toABKModel M) = cstar :=
    (realizesCstar_iff_cstar_eq (toABKModel M) _hcstar).mp hreal
  have hgpos : 0 < M.gamma := M.gamma_pos
  have hsq : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
  have habs : (0 : ℝ) ≤ |Real.log M.gamma| := abs_nonneg _
  have hg : (toABKModel M).gamma ≤ g0 := le_trans hgamma (min_le_left _ _)
  have hgb : (toABKModel M).gamma ≤
      (Cib⁻¹) ^ 10 * (_root_.Algsuperdiff.Section3.Disorder.cstar (toABKModel M)) ^ 10 := by
    rw [hcs]
    exact le_trans hgamma (min_le_right _ _)
  have halpha' : alpha ≤ 1 - C0 * Real.sqrt (toABKModel M).gamma := by
    have hmono : C0 * Real.sqrt M.gamma ≤ Cmax * Real.sqrt M.gamma :=
      mul_le_mul_of_nonneg_right hC0le hsq
    have hgoal : alpha ≤ 1 - C0 * Real.sqrt M.gamma := by linarith only [halpha, hmono]
    exact hgoal
  obtain ⟨X, hXmeas, hXtail, hXae⟩ := hmain (toABKModel M) hcs hg alpha halpha0 halpha' m
  obtain ⟨hsigpos, hsigband⟩ := hbandAll (toABKModel M) hgb m
  rw [hcs] at hsigband
  refine ⟨(_root_.Algsuperdiff.Section3.Annealed.sigmaBar (toABKModel M) m : ℝ), hsigpos, ?_,
    X, hXmeas, ?_, ?_⟩
  · refine le_trans hsigband ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCible hsq) habs) hsigpos.le
  · intro N
    refine le_trans (hXtail N) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hAn : (0 : ℝ) ≤ (1 - alpha) ^ (2 : ℕ) := sq_nonneg _
    have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hdiff : (0 : ℝ) ≤ Cmax - C0 := sub_nonneg.mpr hC0le
    have hexp : -((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C0)) / (C0 * M.gamma) ≤
        -((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - Cmax)) / (Cmax * M.gamma) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hprod : (0 : ℝ) ≤ (1 - alpha) ^ (2 : ℕ) * (N : ℝ) * M.gamma * (Cmax - C0) :=
        mul_nonneg (mul_nonneg (mul_nonneg hAn hNn) hgpos.le) hdiff
      nlinarith only [hprod]
    calc C0 * Real.exp (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C0)) / (C0 * M.gamma))
        ≤ Cmax * Real.exp (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C0)) / (C0 * M.gamma)) :=
          mul_le_mul_of_nonneg_right hC0le (Real.exp_nonneg _)
      _ ≤ Cmax * Real.exp (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - Cmax)) / (Cmax * M.gamma)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hCmaxpos.le
  · have hrpow : ∀ t : ℝ, C0 * Real.rpow (3 : ℝ) t ≤ Cmax * Real.rpow (3 : ℝ) t := fun t =>
      mul_le_mul_of_nonneg_right hC0le (Real.rpow_nonneg (by norm_num) t)
    filter_upwards [hXae] with omega homega
    intro L hL u h g Kg Kh hdir hHg hHh hKinf hgrad x hx n hn hX
    obtain ⟨hd1, hd2⟩ := homega L hL (toRepoH1 u) (toRepoH1 h) g Kg Kh
      ((isDirichletSolutionOn_iff _ _ _ _ _).mp hdir) hHg hHh hKinf hgrad x hx n hn hX
    refine ⟨le_trans hd1 ?_, fun hxm => le_trans (hd2 hxm) ?_⟩
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hrpow _)) _
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hrpow _)) _


end

end AnomalousRegularity
end StatementAudit
end Algsuperdiff
