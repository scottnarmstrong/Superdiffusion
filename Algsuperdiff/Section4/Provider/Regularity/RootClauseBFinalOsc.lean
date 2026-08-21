/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalFunding
import Algsuperdiff.Section4.Provider.Regularity.StepSixInteriorEndpoint

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **`e.oscillation.Holder.bound` at the root's frame, on ONE null set.**

The Step-6 interior endpoint with its entire regime prefix discharged, its
scale pair inside the a.e. block, and its windows written in the carrier the
clause-(B) payload reads.  The `α`-dependent `γ`-gate and the five `γ`-regime
clauses are the only hypotheses on the model; every one of them is produced by
`RootClauseBFinalRegime.exists_rootClauseBGammaFacts`. -/
theorem exists_rootClauseBOsc (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ (C Cann Citer Cosc Cdel : ℝ) (k : ℕ),
      0 < C ∧ 0 < Cann ∧ 0 ≤ Cosc ∧ 0 ≤ Cdel ∧ 11 ≤ k ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ 1 / 256 →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * stepOneS ^ (4 : ℕ)) →
        ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp (stepOneDelta
                  (stepOneC1 d (rootClauseBFundCedos d C Cann k) 1 Citer k) alpha) →
          ∀ m : ℤ, m ≤ m0 →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (L n : ℤ) (v : Fin d → ℤ), m ≤ L → (14 : ℤ) ≤ m - n →
                v ∈ Support.latticeCubeSet d n m →
                Support.triadicLatticePoint n v ∈
                    openCubeSet (originCube d (m - 1)) →
                  RootWindowPayload M
                      (stepOneC1 d (rootClauseBFundCedos d C Cann k) 1 Citer k)
                      alpha n m omega →
                    ∀ (uglob hdat : H1Function (openCubeSet (originCube d m)))
                      (gsrc : Vec d → Vec d) (Khol Kh : ℝ), 0 ≤ Khol → 0 ≤ Kh →
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) uglob hdat gsrc →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Khol gsrc →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kh hdat.grad →
                      ∀ n' kc : ℤ, n ≤ n' → n' ≤ kc → kc ≤ m →
                        (3 : ℝ) ^ (-n') *
                            normalizedL2On
                              (truncatedWindow (Support.triadicLatticePoint n v) m n')
                              (fun y => uglob.toFun y -
                                volumeAverage
                                  (truncatedWindow
                                    (Support.triadicLatticePoint n v) m n')
                                  uglob.toFun) ≤
                          Cosc *
                              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                              ((3 : ℝ) ^ (-kc) *
                                normalizedL2On
                                  (truncatedWindow
                                    (Support.triadicLatticePoint n v) m kc)
                                  (fun y => uglob.toFun y -
                                    volumeAverage
                                      (truncatedWindow
                                        (Support.triadicLatticePoint n v) m kc)
                                      uglob.toFun)) +
                            Cosc *
                              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                              (edFinalDataG M Cdel
                                (Khol * stepFourGagliardoConst d stepOneS) m + 0) := by
  classical
  obtain ⟨C, Cann, hC, hCann, k0, hk0, hres⟩ :=
    edFinal_oscillationHolderBound_interior d hd
  have hk0k : k0 ≤ max k0 11 := le_max_left _ _
  have hk11 : 11 ≤ max k0 11 := le_max_right _ _
  have hk2 : 2 ≤ max k0 11 := le_trans (by norm_num) hk11
  obtain ⟨Cout, Citer, hCout, hCiter, hres'⟩ := hres (max k0 11) hk0k hk2
  have hs0 : (0 : ℝ) < stepOneS := by rw [stepOneS]; norm_num
  have hs2 : stepOneS < 1 / 2 := by rw [stepOneS]; norm_num
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hCoutSq : (0 : ℝ) ≤ Cout * Cout := mul_nonneg hCout.le hCout.le
  refine ⟨C, Cann, Citer, Cout + Cout * Cout,
    edFinalDeltaConst d C (max k0 11) stepOneS, max k0 11, hC, hCann,
    by linarith only [hCout, hCoutSq], edFinalDeltaConst_nonneg d hC.le _ hs0.le,
    hk11, ?_⟩
  intro M m0 Ecap hS hgamma hregC hregAnn hg256 hfree alpha halpha0 halpha1 hsmall m hmm0
  have hC1two : (2 : ℝ) ≤
      stepOneC1 d (rootClauseBFundCedos d C Cann (max k0 11)) 1 Citer (max k0 11) :=
    two_le_stepOneC1 d _ _ _ _
  have hC1pos : (0 : ℝ) <
      stepOneC1 d (rootClauseBFundCedos d C Cann (max k0 11)) 1 Citer (max k0 11) := by
    linarith only [hC1two]
  have hdeltamem := stepOneDelta_mem hC1two halpha0 halpha1
  have hgate := edFunding_of_c1_floor d hC.le hCann.le halpha0.le hC1pos
    (rootClauseBFundFloor_le_stepOneC1 d hC.le hCann.le Citer (max k0 11))
  have hmerge := ae_forall_of_forall_ae_of_countable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (Q := fun p : ℤ × ℤ × (Fin d → ℤ) =>
      m ≤ p.1 ∧ (14 : ℤ) ≤ m - p.2.1 ∧
        p.2.2 ∈ Support.latticeCubeSet d p.2.1 m ∧
        Support.triadicLatticePoint p.2.1 p.2.2 ∈
          openCubeSet (originCube d (m - 1)))
    (fun p hp => hres' M m0 Ecap hS hgamma hregC hregAnn hg256 hfree
      (rootClauseBFundCedos d C Cann (max k0 11)) 1 alpha (le_of_lt halpha1)
      hdeltamem hsmall hgate p.1 m p.2.1 hp.1 hmm0 hp.2.1 p.2.2 hp.2.2.1 hp.2.2.2)
  filter_upwards [hmerge] with omega hom
  intro L n v hL hwin hv hzin hpay uglob hdat gsrc Khol Kh hKhol hKh hsol hgHol hhHol
    n' kc hn' hn'kc hkc
  have hnm : n ≤ m := by omega
  have hbudget := (hpay.2.2.1 v hv).2.2.1
  rw [toNat_sub_cast_real hnm] at hbudget
  obtain ⟨hgL2, hgW⟩ := memLp_pair_of_holderHalf hd1 hKhol hgHol
  have hhW := memLp_two_gagliardoKernel_of_holderHalf hd1 hs0 hs2 hKh hhHol
  obtain ⟨cfam, slope, hmin⟩ :=
    exists_stepThreeWindow_affineMinimizerFamily
      (mem_openCubeSet_of_mem_latticeCubeSet hv) uglob
  exact hom (L, n, v) ⟨hL, hwin, hv, hzin⟩ hpay.1 hbudget uglob hdat gsrc Khol hKhol
    hsol hgL2 hgW hhW hgHol cfam slope hmin n' kc hn' hn'kc hkc

end

end Algsuperdiff.Section4.Provider.Regularity
