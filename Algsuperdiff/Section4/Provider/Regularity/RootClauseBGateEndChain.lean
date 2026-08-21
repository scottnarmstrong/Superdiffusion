/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateGeometry
import Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaChain

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The Step-7 end chain at the gate -/

/-- **The Step-7 end chain with `hgrad` GONE, at `(GATE n')`.**

`StepSevenCaccFinalChain.exists_stepSevenEnd_chain_interior` with the printed
pair `z ∈ □_{m-1}`, `n' ≤ m-1` replaced by the single weaker gate `z + □_{n'} ⊆
□_m`. -/
theorem exists_stepSevenEnd_chain_gate (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (L : ℤ) {alpha : ℝ} {n m k n' mf : ℤ} (Qf : TriadicCube d)
        {a : CoeffFamily d} {g gcacc : Vec d → Vec d} {z c : Vec d}
        (uglob : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        (omega : Cutoff.CutoffSample d)
        (u : ForcedCubeSolution (originCube d k) a g)
        {Ccmp Kg Kd Ks Ctr CB CBc sigma sigmac shomM
          gradM dataG W G H C1 delta Cosc : ℝ} {B : ℕ},
        (∀ y, u.toH1.toFun y = uglob.toFun (y + c)) →
        z ∈ openCubeSet (originCube d m) → k ≤ m →
        truncatedWindow z m k ⊆ (fun y => c + y) '' openCubeSet (originCube d k) →
        IntegrableOn uglob.toFun (truncatedWindow z m k) →
        IntegrableOn (fun x => uglob.toFun x ^ 2) (truncatedWindow z m k) →
        IntegrableOn uglob.toFun ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn (fun x => uglob.toFun x ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn
          (fun x => (uglob.toFun x - volumeAverage ((fun y => c + y) ''
            openCubeSet (originCube d k)) uglob.toFun) ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        0 ≤ CB → 0 ≤ Ks → 0 ≤ Ccmp → 0 < sigma → 0 < shomM →
        0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity (originCube d k) stepSevenCgS g →
        StepSevenLambdaCaps (originCube d (k + 1)) a sigma CB →
        forcedSolutionEnergyNorm (originCube d k) a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS g ≤
          Kd * dataG →
        sigma⁻¹ ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * Kg ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        sigmac ≤ Ccmp * shomM →
        (∀ y, v.toFun y = uglob.toFun (y + z)) →
        (∀ y, v.grad y = uglob.grad (y + z)) →
        (fun y => z + y) '' openCubeSet (originCube d n') ⊆
          openCubeSet (originCube d m) →
        n + 1 ≤ n' - 2 →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v gcacc →
        ForceBesovRegularity (originCube d n') stepOneS gcacc →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ CBc →
        StepSevenLambdaCaps (originCube d (n' + 1))
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) sigmac CBc →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => uglob.toFun x -
                volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              ((cubeScaleFactor (originCube d k))⁻¹ *
                normalizedL2On (truncatedWindow z m k)
                  (fun x => uglob.toFun x -
                    volumeAverage (truncatedWindow z m k) uglob.toFun)) +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              (W * (shomM⁻¹ * G + H))) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) uglob.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) * Real.sqrt Ccmp *
                (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
                  stepSevenBridgeConst stepSevenCgS *
                  (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) gcacc) := by
  obtain ⟨Cchain, hCchainPos, hchain⟩ := exists_stepSevenEnd_chain_of_caps d
  obtain ⟨Cd, hCdPos, hdisp⟩ := exists_stepSevenGradientWithShom_gate_of_caps d
  refine ⟨Cchain, Cd, hCchainPos, hCdPos, ?_⟩
  intro M L alpha n m k n' mf Qf a g gcacc z c uglob v omega u Ccmp Kg Kd Ks Ctr CB CBc
    sigma sigmac shomM gradM dataG W G H C1 delta Cosc B
    hv hz hkm hST hwS hwS2 hwT hwT2 hint hCB hKs hCcmp hsigma hshomM hgradM hdataG
    hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb hcomp
    hval hgradv hgate hcore heq hforcec hC1 halpha0 halpha1 hnm hdelta hgap
    hbudget hCosc hCBc hcapsc hosc
  have hoscHi : (0 : ℝ) ≤ (cubeScaleFactor (originCube d k))⁻¹ *
      normalizedL2On (truncatedWindow z m k)
        (fun x => uglob.toFun x - volumeAverage (truncatedWindow z m k) uglob.toFun) := by
    have hsc : (0 : ℝ) ≤ (cubeScaleFactor (originCube d k))⁻¹ := by
      rw [cubeScaleFactor]
      exact inv_nonneg.mpr (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    exact mul_nonneg hsc (normalizedL2On_nonneg _ _)
  have hdataOsc : (0 : ℝ) ≤ W * (shomM⁻¹ * G + H) :=
    mul_nonneg hW (add_nonneg (mul_nonneg (inv_nonneg.mpr hshomM.le) hG) hH)
  have hgrad := hdisp M L mf m n n' Qf omega uglob v hval hgradv hgate hcore heq
    hforcec hC1 halpha0 halpha1 hnm hdelta hgap hbudget hCosc hCBc hoscHi hdataOsc
    hcapsc hosc
  have hCg : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
      stepSevenCaccConst Cd (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) *
      (Cosc * Real.sqrt (256 / 63 * CBc) + 1) := by
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h2 : (0 : ℝ) ≤ stepSevenCaccConst Cd (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) := stepSevenCaccConst_nonneg _ _ _
    have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBc) + 1 := by
      have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBc))
      linarith only [h4]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  exact hchain u hv hz hkm hST hwS hwS2 hwT hwT2 hint hCg hCB hKs hCcmp hsigma hshomM
    hgradM hdataG hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb hcomp hgrad

/-! ## 2. The same, entered at `t.regularity`'s own Dirichlet datum -/

/-- **The gated Step-7 end chain from the Dirichlet datum alone.**

`StepSevenCaccFinalChain.exists_stepSevenEnd_chain_interior_of_dirichlet` at
`(GATE n')`: the transported solution, its two frame identities, its forced
equation and its forcing-regularity binder are all built inside's gated
builders. -/
theorem exists_stepSevenEnd_chain_gate_of_dirichlet (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (L : ℤ) {alpha : ℝ} {n m k n' mf : ℤ} (Qf : TriadicCube d)
        {a : CoeffFamily d} {g gsrc : Vec d → Vec d} {z c : Vec d}
        (uglob hdat : H1Function (openCubeSet (originCube d m)))
        (omega : Cutoff.CutoffSample d)
        (u : ForcedCubeSolution (originCube d k) a g)
        {Ccmp Kg Kd Ks Ctr CB CBc sigma sigmac shomM
          gradM dataG W G H C1 delta Cosc : ℝ} {B : ℕ},
        (∀ y, u.toH1.toFun y = uglob.toFun (y + c)) →
        z ∈ openCubeSet (originCube d m) → k ≤ m →
        truncatedWindow z m k ⊆ (fun y => c + y) '' openCubeSet (originCube d k) →
        IntegrableOn uglob.toFun (truncatedWindow z m k) →
        IntegrableOn (fun x => uglob.toFun x ^ 2) (truncatedWindow z m k) →
        IntegrableOn uglob.toFun ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn (fun x => uglob.toFun x ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        IntegrableOn
          (fun x => (uglob.toFun x - volumeAverage ((fun y => c + y) ''
            openCubeSet (originCube d k)) uglob.toFun) ^ 2)
          ((fun y => c + y) '' openCubeSet (originCube d k)) →
        0 ≤ CB → 0 ≤ Ks → 0 ≤ Ccmp → 0 < sigma → 0 < shomM →
        0 ≤ gradM → 0 ≤ dataG → 0 ≤ W → 0 ≤ G → 0 ≤ H →
        ForceBesovRegularity (originCube d k) stepSevenCgS g →
        StepSevenLambdaCaps (originCube d (k + 1)) a sigma CB →
        forcedSolutionEnergyNorm (originCube d k) a u ≤ Kg * gradM →
        scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d k) stepSevenCgS g ≤
          Kd * dataG →
        sigma⁻¹ ≤ Ks * shomM⁻¹ →
        Real.sqrt Ks * Kg ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        Ks * Kd ≤ Ctr * Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) →
        sigmac ≤ Ccmp * shomM →
        (fun y => z + y) '' openCubeSet (originCube d n') ⊆
          openCubeSet (originCube d m) →
        n + 1 ≤ n' - 2 →
        Support.IsDirichletSolutionOn
          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) uglob hdat gsrc →
        MemLp gsrc 2
          (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
        MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
          (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
        2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 → n ≤ m →
        delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
        (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
        0 ≤ Cosc → 0 ≤ CBc →
        StepSevenLambdaCaps (originCube d (n' + 1))
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) sigmac CBc →
        ((3 : ℝ) ^ (-n') *
            normalizedL2On (truncatedWindow z m n')
              (fun x => uglob.toFun x -
                volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
          Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              ((cubeScaleFactor (originCube d k))⁻¹ *
                normalizedL2On (truncatedWindow z m k)
                  (fun x => uglob.toFun x -
                    volumeAverage (truncatedWindow z m k) uglob.toFun)) +
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
              (W * (shomM⁻¹ * G + H))) →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n + 1)) uglob.grad ≤
            (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) * Real.sqrt Ccmp *
                (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
                  stepSevenBridgeConst stepSevenCgS *
                  (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) *
                Real.rpow (3 : ℝ) (stepSixExponent alpha n m) *
                (gradM + Real.sqrt shomM⁻¹ * dataG) +
              (Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) *
                  stepSevenCaccConst Cc (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega)) *
                  (Cosc * Real.sqrt (256 / 63 * CBc) + 1)) *
                Real.rpow (3 : ℝ) (3 / 4 * stepSixExponent alpha n m) *
                (Real.sqrt Ccmp *
                  (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) +
                  stepSevenCaccDataM (originCube d n')
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega))
                    (fun x => -gsrc (x + z))) := by
  obtain ⟨Cch, Cc, hCch, hCc, hmain⟩ := exists_stepSevenEnd_chain_gate d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M L alpha n m k n' mf Qf a g gsrc z c uglob hdat omega u Ccmp Kg Kd Ks Ctr CB CBc
    sigma sigmac shomM gradM dataG W G H C1 delta Cosc B
    hv hz hkm hST hwS hwS2 hwT hwT2 hint hCB hKs hCcmp hsigma hshomM hgradM hdataG
    hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb hcomp
    hgate hcore hsol hgL2 hgW hC1 halpha0 halpha1 hnm hdelta hgap
    hbudget hCosc hCBc hcapsc hosc
  obtain ⟨v, hval, hgradv, heq⟩ :=
    exists_stepSevenCaccGateSolution (n' := n') (mf := mf) M L Qf omega hgate hsol
  have hforcec := forceBesovRegularity_stepSevenCacc_gate (n' := n') hgate hgL2 hgW
  exact hmain M L Qf uglob v omega u hv hz hkm hST hwS hwS2 hwT hwT2 hint hCB hKs hCcmp
    hsigma hshomM hgradM hdataG hW hG hH hforce hcaps hgradE hdataB htrShom hKgb hKdb
    hcomp hval hgradv hgate hcore heq hforcec hC1 halpha0 halpha1 hnm hdelta hgap
    hbudget hCosc hCBc hcapsc hosc

end

end Algsuperdiff.Section4.Provider.Regularity
