/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBInputs

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The composite prefactor -/

/-- The Step-7c gradient-display constant `C_g = 3^{3d+1/4}·C_cacc·(C_osc√C_lam+1)`
of `StepSevenCaccFinalDisplay`. -/
def rootClauseBCg (d : ℕ) (Ccacc Cosc CBc : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) * Ccacc *
    (Cosc * Real.sqrt (256 / 63 * CBc) + 1)

/-- **The clause-(B) prefactor**, the composite constant the outer collapse
produces: the oscillation half's `C_g√C_cmp·(embedding·bridge·Poincaré·C_tr)`
plus the data half's `C_g(√C_cmp·C_WG + C_dM)`, at `C_cmp = 4`. -/
def rootClauseBPrefactor (d : ℕ) [NeZero d] (Cch Ccacc Cosc CBc CB Ctr CWG CdM : ℝ) : ℝ :=
  rootClauseBCg d Ccacc Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) +
    rootClauseBCg d Ccacc Cosc CBc * (Real.sqrt 4 * CWG + CdM)

/-! ## 2. Two scalar steps -/

/-- `1 ≤ 3^{E/4}` at `E ≥ 0`: the slack that discharges the two `K_tr` dominations
once `K_s = 1`. -/
theorem one_le_rpow_three_quarter {E : ℝ} (hE : 0 ≤ E) :
    (1 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 4 * E) := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith only [hE] : (0 : ℝ) ≤ 1 / 4 * E)
  rwa [Real.rpow_zero] at h

/-- The final constant enlargement (`RootAssemblyParameters` §3's pattern). -/
theorem clauseB_const_mono {A P Cest R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hP : P ≤ Cest) (h : A ≤ P * R * T) : A ≤ Cest * R * T := by
  have h1 : P * R ≤ Cest * R := mul_le_mul_of_nonneg_right hP hR
  have h2 : P * R * T ≤ Cest * R * T := mul_le_mul_of_nonneg_right h1 hT
  linarith only [h, h2]

/-! ## 3. Clause (B), composed -/

/-- **Clause (B) of `RootAssemblyConditional.RootLatticeDisplay`**, at an
arbitrary lattice-interior centre `z`.

`hosc` is stated V in the shape
`StepSixInteriorEndpoint.edFinal_oscillationHolderBound_interior` concludes at
`m' = m-1`, so supplying it is a single application's producer. -/
theorem rootClauseB_display_interior (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {alpha : ℝ} {n m n' : ℤ} {z : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kd CB CBc Cdel Cosc CdM C1 delta Cest : ℝ} {B : ℕ},
          z ∈ openCubeSet (originCube d (m - 1)) → m ≤ m0 →
          n' ≤ m - 1 → n + 1 ≤ n' - 2 → n ≤ m →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          MemLp gsrc 2
              (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
          MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
              (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
          0 ≤ Khol → 0 ≤ Kd → 0 ≤ CB → 0 ≤ CBc → 0 ≤ Cdel → 0 ≤ Cosc → 0 ≤ CdM →
          2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 →
          delta ≤ C1⁻¹ * (1 - alpha) → n' - n ≤ (B : ℤ) + 6 →
          (B : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1) →
          StepSevenLambdaCaps (originCube d m)
              (Support.fluxCorrectedCoeffFamily M L m (originCube d m)
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M m : ℝ)) CB →
          StepSevenLambdaCaps (originCube d (n' + 1))
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc →
          scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (m - 1))
              stepSevenCgS (fun x => -gsrc (x + z)) ≤
            Kd * edFinalDataOscG Khol m →
          stepSevenCaccDataM (originCube d n')
              (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
                (Cutoff.translateCutoffSample z omega))
              (fun x => -gsrc (x + z)) ≤
            CdM * (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
              edFinalDataOscG Khol m) →
          ((3 : ℝ) ^ (-n') *
              normalizedL2On (truncatedWindow z m n')
                (fun x => uglob.toFun x -
                  volumeAverage (truncatedWindow z m n') uglob.toFun) ≤
            Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                ((3 : ℝ) ^ (-(m - 1)) *
                  normalizedL2On (truncatedWindow z m (m - 1))
                    (fun x => uglob.toFun x -
                      volumeAverage (truncatedWindow z m (m - 1)) uglob.toFun)) +
              Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                (edFinalDataG M Cdel
                  (Khol * stepFourGagliardoConst d stepOneS) m + 0)) →
          rootClauseBPrefactor d Cch
              (stepSevenCaccConst Cc (originCube d n')
                (Support.fluxCorrectedCoeffFamily M L (n' + 1)
                  (originCube d (n' + 1)) (Cutoff.translateCutoffSample z omega)))
              Cosc CBc CB (max (Real.sqrt ((3 : ℝ) ^ d)) Kd)
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) CdM ≤
            Cest →
          Real.sqrt M.nu *
              normalizedL2On (truncatedWindow z m (n + 1))
                (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
            ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (Real.sqrt M.nu *
                  normalizedL2On (openCubeSet (originCube d m))
                    (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol) := by
  obtain ⟨Cch, Cc, hCch, hCc, hchain⟩ := exists_stepSevenEnd_chain_interior_of_dirichlet d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L alpha n m n' z omega uglob hdat gsrc Khol Kd CB CBc Cdel
    Cosc CdM C1 delta Cest B hzin hmm0 hn' hcore hnm hsol hgL2 hgW hKhol hKd hCB hCBc
    hCdel hCosc hCdM hC1 halpha0 halpha1 hdelta hgap hbudget hcaps hcapsc hdataB
    hdataM hosc hCest
  -- geometry at the top interior scale
  have hzm : z ∈ openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (by omega) hzin
  have hsub : translateSet z (openCubeSet (originCube d (m - 1))) ⊆
      openCubeSet (originCube d m) := by
    rw [← image_add_eq_translateSet]
    exact image_add_subset_openCubeSet_of_mem_inner hzin (le_refl (m - 1))
  have hWeq : truncatedWindow z m (m - 1) =
      (fun y => z + y) '' openCubeSet (originCube d (m - 1)) := by
    rw [truncatedWindow_eq_translateSet_of_mem_inner hzin (le_refl (m - 1)),
      image_add_eq_translateSet]
  have hTsub : (fun y => z + y) '' openCubeSet (originCube d (m - 1)) ⊆
      openCubeSet (originCube d m) := by
    rw [image_add_eq_translateSet]; exact hsub
  have hTtop : volume ((fun y => z + y) '' openCubeSet (originCube d (m - 1))) ≠ ⊤ :=
    volume_image_add_openCubeSet_ne_top z (m - 1)
  have hStop : volume (truncatedWindow z m (m - 1)) ≠ ⊤ :=
    (volume_truncatedWindow_lt_top z m (m - 1)).ne
  -- the solution object at the lattice centre, at the free flux pair `(m, □_m)`
  obtain ⟨v, hval, hgradid, heqv⟩ :=
    exists_stepSevenCaccInteriorSolution (n' := m - 1) (mf := m) M L
      (originCube d m) omega hzin (le_refl (m - 1)) hsol
  have hgradE : forcedSolutionEnergyNorm (originCube d (m - 1))
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m)
          (Cutoff.translateCutoffSample z omega))
        (⟨v, heqv⟩ : ForcedCubeSolution (originCube d (m - 1))
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m)
            (Cutoff.translateCutoffSample z omega)) (fun x => -gsrc (x + z))) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m)) uglob.grad := by
    rw [forcedSolutionEnergyNorm_fluxCorrected_eq_nuGradNorm M L m m (m - 1)
      (originCube d m) omega _ uglob.grad hgradid hzin (le_refl (m - 1))]
    exact stepSevenNuGradNorm_inner_le_cube d (le_of_lt M.nu_pos) hzin uglob
  -- the caps binder at `□_{(m-1)+1}`
  have hcaps' : StepSevenLambdaCaps (originCube d (m - 1 + 1))
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m)
        (Cutoff.translateCutoffSample z omega))
      ((Annealed.sigmaBar M m : ℝ)) CB := by
    rw [show m - 1 + 1 = m by ring]
    exact hcaps
  -- the two `σ̄` slots
  have hsigmaPos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have htrShom : ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
      1 * ((Annealed.sigmaBar M m : ℝ))⁻¹ := by
    rw [one_mul]
  have hcomp : (Annealed.sigmaBar M (n' + 1) : ℝ) ≤ 4 * (Annealed.sigmaBar M m : ℝ) :=
    sigmaBar_le_four_mul_sigmaBar M hS (by omega) hmm0
  -- the two `K_tr` dominations at `K_s = 1`
  have hE : (0 : ℝ) ≤ stepSixExponent alpha n m := by
    have hc : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    rw [stepSixExponent]
    exact mul_nonneg (by linarith only [halpha1]) (by linarith only [hc])
  have hone := one_le_rpow_three_quarter (E := stepSixExponent alpha n m) hE
  have hCtr0 : (0 : ℝ) ≤ max (Real.sqrt ((3 : ℝ) ^ d)) Kd :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hKgb : Real.sqrt 1 * Real.sqrt ((3 : ℝ) ^ d) ≤
      max (Real.sqrt ((3 : ℝ) ^ d)) Kd *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
    have h1 : Real.sqrt ((3 : ℝ) ^ d) ≤ max (Real.sqrt ((3 : ℝ) ^ d)) Kd :=
      le_max_left _ _
    have h2 : max (Real.sqrt ((3 : ℝ) ^ d)) Kd * 1 ≤
        max (Real.sqrt ((3 : ℝ) ^ d)) Kd *
          Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
      mul_le_mul_of_nonneg_left hone hCtr0
    rw [Real.sqrt_one, one_mul]
    linarith only [h1, h2]
  have hKdb : 1 * Kd ≤
      max (Real.sqrt ((3 : ℝ) ^ d)) Kd *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
    have h1 : Kd ≤ max (Real.sqrt ((3 : ℝ) ^ d)) Kd := le_max_right _ _
    have h2 : max (Real.sqrt ((3 : ℝ) ^ d)) Kd * 1 ≤
        max (Real.sqrt ((3 : ℝ) ^ d)) Kd *
          Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
      mul_le_mul_of_nonneg_left hone hCtr0
    rw [one_mul]
    linarith only [h1, h2]
  -- the `dataOsc` slot (items (i) and (ii))
  have hW0 : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hgamma hCdel) (stepFourGagliardoConst_nonneg d _)
  have hG0 : (0 : ℝ) ≤ edFinalDataOscG Khol m := edFinalDataOscG_nonneg hKhol m
  have hoscChain := hosc
  rw [edFinalDataG_eq_dataOsc_scaled M Cdel Khol (stepFourGagliardoConst d stepOneS) m,
    ← cubeScaleFactor_originCube_inv d (m - 1)] at hoscChain
  -- the chain
  have hmain := hchain M L (originCube d (n' + 1)) uglob hdat omega ⟨v, heqv⟩
    (Ccmp := 4) (Kg := Real.sqrt ((3 : ℝ) ^ d)) (Kd := Kd) (Ks := 1)
    (Ctr := max (Real.sqrt ((3 : ℝ) ^ d)) Kd) (CB := CB) (CBc := CBc)
    (sigma := (Annealed.sigmaBar M m : ℝ)) (sigmac := (Annealed.sigmaBar M (n' + 1) : ℝ))
    (shomM := (Annealed.sigmaBar M m : ℝ))
    (gradM := stepSevenNuGradNorm (M.nu : ℝ) (openCubeSet (originCube d m)) uglob.grad)
    (dataG := edFinalDataOscG Khol m)
    (W := edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS)
    (G := edFinalDataOscG Khol m) (H := 0) (C1 := C1) (delta := delta) (Cosc := Cosc)
    (B := B) hval hzm (by omega) (hWeq ▸ Set.Subset.refl _)
    (integrableOn_toFun_subset uglob (truncatedWindow_subset_domain z m (m - 1)) hStop)
    (integrableOn_sq_toFun_subset uglob (truncatedWindow_subset_domain z m (m - 1)) hStop)
    (integrableOn_toFun_subset uglob hTsub hTtop)
    (integrableOn_sq_toFun_subset uglob hTsub hTtop)
    (integrableOn_sub_sq_toFun_subset uglob hTsub hTtop _)
    hCB (by norm_num) (by norm_num) hsigmaPos hsigmaPos
    (stepSevenNuGradNorm_nonneg _ _ _) hG0 hW0 hG0 (le_refl 0)
    (forceBesovRegularity_stepSevenCacc_interior (n' := m - 1) hzin (le_refl (m - 1))
      hgL2 hgW)
    hcaps' hgradE hdataB htrShom hKgb hKdb hcomp hzin hn' hcore hsol hgL2 hgW hC1
    halpha0 halpha1 hnm hdelta hgap hbudget hCosc hCBc hcapsc hoscChain
  -- the outer collapse (item (iv))
  have hCgnn : (0 : ℝ) ≤ rootClauseBCg d
      (stepSevenCaccConst Cc (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
          (Cutoff.translateCutoffSample z omega))) Cosc CBc := by
    have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBc) + 1 := by
      have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBc))
      linarith only [h4]
    rw [rootClauseBCg]
    exact mul_nonneg (mul_nonneg h1 (stepSevenCaccConst_nonneg _ _ _)) h3
  have hXnn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS *
      (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) *
      max (Real.sqrt ((3 : ℝ) ^ d)) Kd := by
    have hb : (0 : ℝ) ≤ Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB) := by
      have h1 : (0 : ℝ) ≤ Cch * 64 := by linarith only [hCch]
      have h2 : (0 : ℝ) ≤ Real.sqrt (32 / 7 * CB) + 32 / 7 * CB := by
        have := Real.sqrt_nonneg (32 / 7 * CB)
        linarith only [this, hCB]
      exact mul_nonneg h1 h2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) hb) hCtr0
  have hKmain : (0 : ℝ) ≤ rootClauseBCg d
        (stepSevenCaccConst Cc (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L (n' + 1) (originCube d (n' + 1))
            (Cutoff.translateCutoffSample z omega))) Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) *
        max (Real.sqrt ((3 : ℝ) ^ d)) Kd) :=
    mul_nonneg (mul_nonneg hCgnn (Real.sqrt_nonneg 4)) hXnn
  have hcoll := rootClauseB_collapse (CdG := 1) (Lg := edFinalDataOscG Khol m)
    hKmain hCgnn (Real.sqrt_nonneg 4) hW0 hCdM hE
    (stepSevenNuGradNorm_nonneg _ _ _) hG0 (mul_nonneg hW0 hG0)
    (stepSevenCaccDataM_nonneg _ _
      (forceBesovRegularity_stepSevenCacc_interior (n' := n') hzin hn' hgL2 hgW))
    (by rw [one_mul]) (le_refl _) hdataM hmain
  rw [max_self, mul_one] at hcoll
  -- into the root's own carrier and constant
  rw [stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On (le_of_lt M.nu_pos),
    stepSixExponent, edFinalDataOscG,
    ← mul_assoc (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹)
      (Real.rpow (3 : ℝ) ((m : ℝ) / 2)) Khol] at hcoll
  rw [rootClauseBPrefactor] at hCest
  refine clauseB_const_mono (Real.rpow_pos_of_pos (by norm_num) _).le ?_ hCest hcoll
  have h1 : (0 : ℝ) ≤ Real.sqrt M.nu *
      normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (uglob.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (normalizedL2On_nonneg _ _)
  have h2 : (0 : ℝ) ≤ Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos (by norm_num) _).le) hKhol
  linarith only [h1, h2]

end

end Algsuperdiff.Section4.Provider.Regularity
