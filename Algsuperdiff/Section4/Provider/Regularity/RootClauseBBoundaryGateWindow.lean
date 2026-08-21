/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateBoundaryC1
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBGatePayload
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalArith

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The boundary prefactor is the interior one with the two data legs summed -/

/-- **The boundary prefactor, re-read.**

's `rootClauseBBoundaryPrefactor` charges the two data legs separately
(`√C_cmp·C_WG` and `√C_cmp·C_WH`); the interior `rootClauseBPrefactor` charges
one.  Since both enter the same bracket additively, the boundary constant is
the interior constant at `C_WG + C_WH`.  A ring identity — no estimate. -/
theorem rootClauseBBoundaryPrefactor_eq_prefactor (d : ℕ) [NeZero d]
    (Cch Ccacc Cosc CBc CB Ctr CWG CWH CdM : ℝ) :
    rootClauseBBoundaryPrefactor d Cch Ccacc Cosc CBc CB Ctr CWG CWH CdM =
      rootClauseBPrefactor d Cch Ccacc Cosc CBc CB Ctr (CWG + CWH) CdM := by
  rw [rootClauseBBoundaryPrefactor, rootClauseBPrefactor]
  ring

theorem rootClauseBBoundaryPrefactor_mono_ccacc (d : ℕ) [NeZero d]
    {Cch Ccacc Ccacc' Cosc CBc CB Ctr CWG CWH CdM : ℝ} (hCch : 0 ≤ Cch)
    (hCosc : 0 ≤ Cosc) (hCB : 0 ≤ CB) (hCtr : 0 ≤ Ctr) (hCWG : 0 ≤ CWG)
    (hCWH : 0 ≤ CWH) (hCdM : 0 ≤ CdM) (h : Ccacc ≤ Ccacc') :
    rootClauseBBoundaryPrefactor d Cch Ccacc Cosc CBc CB Ctr CWG CWH CdM ≤
      rootClauseBBoundaryPrefactor d Cch Ccacc' Cosc CBc CB Ctr CWG CWH CdM := by
  rw [rootClauseBBoundaryPrefactor_eq_prefactor, rootClauseBBoundaryPrefactor_eq_prefactor]
  exact rootClauseBPrefactor_mono_ccacc d hCch hCosc hCB hCtr
    (by linarith only [hCWG, hCWH]) hCdM h

theorem rootClauseBBoundaryPrefactor_mono_data (d : ℕ) [NeZero d]
    {Cch Ccacc Cosc CBc CBc' CB CB' Ctr CWG CWG' CWH CWH' CdM CdM' : ℝ}
    (hCch : 0 ≤ Cch) (hCcacc : 0 ≤ Ccacc) (hCosc : 0 ≤ Cosc) (hCB : 0 ≤ CB)
    (hCtr : 0 ≤ Ctr) (hCWG : 0 ≤ CWG) (hCWH : 0 ≤ CWH) (hCdM : 0 ≤ CdM)
    (hBc : CBc ≤ CBc') (hB : CB ≤ CB') (hWG : CWG ≤ CWG') (hWH : CWH ≤ CWH')
    (hdM : CdM ≤ CdM') :
    rootClauseBBoundaryPrefactor d Cch Ccacc Cosc CBc CB Ctr CWG CWH CdM ≤
      rootClauseBBoundaryPrefactor d Cch Ccacc Cosc CBc' CB' Ctr CWG' CWH' CdM' := by
  rw [rootClauseBBoundaryPrefactor_eq_prefactor, rootClauseBBoundaryPrefactor_eq_prefactor]
  exact rootClauseBPrefactor_mono_data d hCch hCcacc hCosc hCB hCtr
    (by linarith only [hCWG, hCWH]) hCdM hBc hB (by linarith only [hWG, hWH]) hdM

/-! ## 2. The boundary three-leg display, off the root's own a.e. block -/

/-- **Clause (A) of the a.e. lattice display at a boundary lattice centre, from
`RootWindowPayload` and `hosc` ALONE, at `(GATE m-2)`.**

's pointwise boundary display with its coarse scale `k_c`, its inner scale `n'`
and its bad-scale count `B`'s joint pigeonhole and its four non-oscillation
payload fields's gated geometry.  The funding line is stated at the `ω`-free
Caccioppoli constant.  No scale and no `MemLp` binder is caller data. -/
theorem rootClauseB_display_gate_boundaryC1_of_windowPayload (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) (Cb C : ℝ) (k : ℕ) {C1 alpha : ℝ} {n m : ℤ} {x : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d} {Khol Kh CB Cosc Cest : ℝ},
          m ≤ m0 → n ≤ m → m ≤ L →
          (∀ (k' n0 : ℤ) (v0 : Fin d → ℤ),
            omega ∈ stepThreeGoodEvent M (stepOneDelta C1 alpha) k'
                (Support.triadicLatticePoint n0 v0) →
              ∀ L' : ℤ, k' ≤ L' →
                StepSevenLambdaCaps (originCube d k')
                  (Support.fluxCorrectedCoeffFamily M L' k' (originCube d k')
                    (Cutoff.translateCutoffSample
                      (Support.triadicLatticePoint n0 v0) omega))
                  ((Annealed.sigmaBar M k' : ℝ)) CB) →
          RootWindowPayload M C1 alpha n m omega →
          x ∈ openCubeSet (originCube d m) →
          (fun y => offGridCentre n x + y) '' openCubeSet (originCube d (m - 2)) ⊆
            openCubeSet (originCube d m) →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
              (1 / 2) Khol gsrc →
          0 ≤ Khol → 0 ≤ Kh → 0 ≤ CB → 0 ≤ C → 0 ≤ Cosc →
          2 * (d : ℝ) + 2 ≤ C1 → 0 ≤ alpha → alpha ≤ 1 →
          (∀ n' kc : ℤ, n ≤ n' → n' ≤ kc → kc ≤ m →
            (3 : ℝ) ^ (-n') *
                normalizedL2On (truncatedWindow (offGridCentre n x) m n')
                  (fun y => uglob.toFun y -
                    volumeAverage (truncatedWindow (offGridCentre n x) m n')
                      uglob.toFun) ≤
              Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                  ((3 : ℝ) ^ (-kc) *
                    normalizedL2On (truncatedWindow (offGridCentre n x) m kc)
                      (fun y => uglob.toFun y -
                        volumeAverage (truncatedWindow (offGridCentre n x) m kc)
                          uglob.toFun)) +
                Cosc * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                  (edFinalDataG M (edBoundaryCbd d Cb C k)
                      (Khol * stepFourGagliardoConst d stepOneS) m +
                    edBoundaryDataHPrinted d Cb C k Kh m)) →
          rootClauseBBoundaryPrefactor d Cch (rootClauseBCaccUniform Cc CB) Cosc CB CB
              (rootClauseBTopCtr d (rootClauseBDataBConst d))
              (edFinalDataOscW M (edBoundaryCbd d Cb C k) *
                stepFourGagliardoConst d stepOneS)
              (boundaryCWH d Cb C k) (rootClauseBDataMConst d CB) ≤ Cest →
          Real.sqrt M.nu *
              normalizedL2On (truncatedWindow (offGridCentre n x) m (n + 1))
                (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
            ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (Real.sqrt M.nu *
                  normalizedL2On (openCubeSet (originCube d m))
                    (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol +
                Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  obtain ⟨Cch, Cc, hCch, hCc, hmain⟩ := rootClauseB_display_gate_boundaryC1_ofStepSix d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L Cb C k C1 alpha n m x omega uglob hdat gsrc Khol Kh CB Cosc
    Cest hmm0 hnm hmL hmerge hwin hx hgate hsol hgHol hKhol hKh hCB hC hCosc hC1 halpha0
    halpha1 hosc hCest
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  obtain ⟨hgL2, hgW⟩ := memLp_pair_of_holderHalf hd hKhol hgHol
  obtain ⟨-, -, hbudgetW, -⟩ := hwin
  have hv : offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
    offGridLatticeIndex_mem_of_mem_cube n hx
  have hcard := (hbudgetW _ hv).2.2.1
  obtain ⟨j, kk, hjlo, hjk, hkhi, hgapLo, hgapHi, hcapsj, hcapsk⟩ :=
    exists_rootClauseBCapsPair hmerge hbudgetW hv hmL
  obtain ⟨kc, rfl⟩ : ∃ kc : ℤ, kk = kc + 1 := ⟨kk - 1, by ring⟩
  obtain ⟨n', rfl⟩ : ∃ n' : ℤ, j = n' + 1 := ⟨j - 1, by ring⟩
  have hgateKc : (fun y => offGridCentre n x + y) '' openCubeSet (originCube d kc) ⊆
      openCubeSet (originCube d m) :=
    image_add_subset_openCubeSet_of_gate_le (by omega) hgate
  have hgateN : (fun y => offGridCentre n x + y) '' openCubeSet (originCube d n') ⊆
      openCubeSet (originCube d m) :=
    image_add_subset_openCubeSet_of_gate_le (by omega) hgate
  have hCWG0 : (0 : ℝ) ≤
      edFinalDataOscW M (edBoundaryCbd d Cb C k) * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hgamma (edBoundaryCbd_nonneg d Cb hC k))
      (stepFourGagliardoConst_nonneg d _)
  refine hmain M m0 Ecap hS hgamma L Cb C k omega uglob hdat hgateKc hmm0 (by omega)
    (by omega) hnm (by omega) (by omega) (by omega) hsol hgL2 hgW hKhol hKh
    (rootClauseBDataBConst_nonneg d) hCB hCB hC hCosc (rootClauseBDataMConst_nonneg d CB)
    hC1 halpha0 halpha1 (le_refl _) (by omega) hcard hcapsk hcapsj
    (rootClauseB_dataB_gate hgateKc (by omega) hKhol hgHol hgL2 hgW)
    (rootClauseB_dataM_gate hS hgamma hmm0 (by omega) hgateN hKhol hCB hgHol hgL2 hgW
      hcapsj)
    (hosc n' kc (by omega) (by omega) (by omega)) ?_
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M (n' + 1) : ℝ) :=
    (Annealed.sigmaBar M (n' + 1)).2
  have hcacc := stepSevenCaccConst_le_uniform (k := n') hCc hsigma hcapsj
  exact le_trans (rootClauseBBoundaryPrefactor_mono_ccacc d hCch.le hCosc hCB
    (rootClauseBTopCtr_nonneg d _) hCWG0 (boundaryCWH_nonneg d Cb hC k)
    (rootClauseBDataMConst_nonneg d CB) hcacc) hCest

end

end Algsuperdiff.Section4.Provider.Regularity
