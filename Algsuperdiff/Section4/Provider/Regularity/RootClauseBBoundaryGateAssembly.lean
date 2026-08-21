/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBBoundaryGateWindow
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBBoundaryOscFloor
import Algsuperdiff.Section4.Provider.GoodEvents.InductionState

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The boundary prefactor is nonnegative -/

/-- The boundary prefactor at nonnegative data. -/
theorem rootClauseBBoundaryPrefactor_nonneg (d : ℕ) [NeZero d]
    {Cch Ccacc Cosc CBc CB Ctr CWG CWH CdM : ℝ} (hCch : 0 ≤ Cch) (hCcacc : 0 ≤ Ccacc)
    (hCosc : 0 ≤ Cosc) (hCB : 0 ≤ CB) (hCtr : 0 ≤ Ctr) (hCWG : 0 ≤ CWG)
    (hCWH : 0 ≤ CWH) (hCdM : 0 ≤ CdM) :
    0 ≤ rootClauseBBoundaryPrefactor d Cch Ccacc Cosc CBc CB Ctr CWG CWH CdM := by
  have hCg : (0 : ℝ) ≤ rootClauseBCg d Ccacc Cosc CBc :=
    rootClauseBCg_nonneg d hCcacc hCosc
  have hbr : (0 : ℝ) ≤ Real.sqrt (32 / 7 * CB) + 32 / 7 * CB := by
    have h5 := Real.sqrt_nonneg (32 / 7 * CB)
    linarith only [h5, hCB]
  have hX : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS *
      (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) ?_) hCtr
    exact mul_nonneg (by linarith only [hCch]) hbr
  have hY : (0 : ℝ) ≤ Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM := by
    have h1 := mul_nonneg (Real.sqrt_nonneg (4 : ℝ)) hCWG
    have h2 := mul_nonneg (Real.sqrt_nonneg (4 : ℝ)) hCWH
    linarith only [h1, h2, hCdM]
  have hleft : (0 : ℝ) ≤ rootClauseBCg d Ccacc Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) :=
    mul_nonneg (mul_nonneg hCg (Real.sqrt_nonneg 4)) hX
  have hright : (0 : ℝ) ≤ rootClauseBCg d Ccacc Cosc CBc *
      (Real.sqrt 4 * CWG + Real.sqrt 4 * CWH + CdM) := mul_nonneg hCg hY
  rw [rootClauseBBoundaryPrefactor]
  exact add_nonneg hleft hright

/-! ## 2. The gated-region boundary endpoint -/

/-- **The boundary three-leg display, almost surely, on the gated region.**

The boundary-centre half of the root's lattice display, at a `C_est` fixed
before the model and the sample are chosen, with `C_edos` free above this
lane's own floor and the region stated as the caller-visible gate `z + □_{m-2}
⊆ □_m`. -/
theorem rootClauseB_display_gate_boundary_final_floor (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cfl Citer Cest : ℝ) (k : ℕ),
      1 ≤ Cfl ∧ 0 ≤ Cest ∧ 11 ≤ k ∧
      ∀ Cedos : ℝ, Cfl ≤ Cedos →
        ∃ gamma0 : ℝ, 0 < gamma0 ∧
          ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
              ∀ m : ℤ,
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n L : ℤ, n ≤ m → m ≤ L →
                    RootWindowPayload M (stepOneC1 d Cedos 1 Citer k) alpha n m omega →
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
                        Support.HasGradientOn (openCubeSet (originCube d m))
                          h.toFun h.grad →
                        ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                          ((fun y => offGridCentre n x + y) ''
                              openCubeSet (originCube d (m - 2)) ⊆
                            openCubeSet (originCube d m) →
                            Real.sqrt M.nu *
                                Support.normalizedL2On
                                  (truncatedWindow (offGridCentre n x) m (n + 1))
                                  (fun y => Real.sqrt (vecNormSq (u.grad y)))
                              ≤ Cest *
                                  Real.rpow (3 : ℝ)
                                    ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                                (Real.sqrt M.nu *
                                    Support.normalizedL2On
                                      (openCubeSet (originCube d m))
                                      (fun y => Real.sqrt (vecNormSq (u.grad y))) +
                                  Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                                  Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) := by
  classical
  obtain ⟨C, Ccap, Cann, Cb, Cflo, Citer, Cosc, kb, hC, hCcap, hCann, hCb, hCflo,
    hCosc, hk10, hoscprod⟩ := exists_rootClauseBOsc_boundary_floor d hd
  obtain ⟨Ccaps, hCcaps, hcapsprod⟩ := ae_stepSevenLambdaCaps_merged d
  obtain ⟨Cind, hCind6, -, hind⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d 0
  obtain ⟨Cch, Cc, hCch, hCc, hend⟩ := rootClauseB_display_gate_boundaryC1_of_windowPayload d
  have hCindpos : (0 : ℝ) < Cind := by linarith only [hCind6]
  have hCbd : (0 : ℝ) ≤ edBoundaryCbd d Cb C kb := edBoundaryCbd_nonneg d Cb hC.le kb
  have hCWH : (0 : ℝ) ≤ boundaryCWH d Cb C kb := boundaryCWH_nonneg d Cb hC.le kb
  set Cmax : ℝ := max (max C Ccap) Ccaps with hCmaxDef
  have hCmaxpos : (0 : ℝ) < Cmax :=
    lt_of_lt_of_le hC (le_trans (le_max_left _ _) (le_max_left _ _))
  set CBu : ℝ := rootClauseBCapsUniform d Ccaps with hCBuDef
  have hCBu : (0 : ℝ) ≤ CBu := rootClauseBCapsUniform_nonneg d Ccaps
  set CWGu : ℝ := rootClauseBOscWUniform (edBoundaryCbd d Cb C kb) *
    stepFourGagliardoConst d stepOneS with hCWGuDef
  have hCWGu0 : (0 : ℝ) ≤ CWGu := by
    rw [hCWGuDef]
    exact mul_nonneg (rootClauseBOscWUniform_nonneg hCbd)
      (stepFourGagliardoConst_nonneg d _)
  refine ⟨Cflo, Citer,
    rootClauseBBoundaryPrefactor d Cch (rootClauseBCaccUniform Cc CBu) Cosc CBu CBu
      (rootClauseBTopCtr d (rootClauseBDataBConst d)) CWGu (boundaryCWH d Cb C kb)
      (rootClauseBDataMConst d CBu),
    kb + 1, hCflo,
    rootClauseBBoundaryPrefactor_nonneg d hCch.le (rootClauseBCaccUniform_nonneg Cc CBu)
      hCosc hCBu (rootClauseBTopCtr_nonneg d _) hCWGu0 hCWH
      (rootClauseBDataMConst_nonneg d CBu), by omega, ?_⟩
  intro Cedos hfloor
  set C1 : ℝ := stepOneC1 d Cedos 1 Citer (kb + 1) with hC1Def
  have hC1two : (2 : ℝ) ≤ C1 := two_le_stepOneC1 d Cedos 1 Citer (kb + 1)
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1two]
  obtain ⟨gamma0, hgamma0, hfacts⟩ :=
    exists_rootClauseBGammaFacts d (C := Cmax) (Cann := Cann) (Cind := Cind)
      (C1 := C1) (Crg := Crg) hcstar hCmaxpos hCann hCindpos hC1pos hCrg
  refine ⟨gamma0, hgamma0, ?_⟩
  intro M hcs hgammale alpha halpha0 halpha m
  have hfact := hfacts M hcs hgammale
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsqrtpos : (0 : ℝ) < Crg * Real.sqrt M.gamma :=
    mul_pos hCrg (Real.sqrt_pos.mpr hg0)
  have halpha1 : alpha < 1 := by linarith only [halpha, hsqrtpos]
  have hcs10 : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) :=
    pow_nonneg ((Disorder.cstar_characterization M).1).le 10
  have hregC : M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hC (le_trans (le_max_left _ _) (le_max_left _ _))) hcs10)
  have hregCap : M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCcap (le_trans (le_max_right _ _) (le_max_left _ _))) hcs10)
  have hregCaps : M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right
      (inv_anti₀ hCcaps (le_max_right _ _)) hcs10)
  have hsmall := hfact.smallEp alpha halpha0 halpha
  obtain ⟨Ecap, -, -, hstate⟩ := hind M hfact.regimeInd
  have hdeltamem := stepOneDelta_mem hC1two halpha0 halpha1
  have haeOsc := hoscprod Cedos hfloor M m Ecap (hstate m) hfact.ltHalf hregC hregCap
    hfact.regimeAnn hfact.le256 alpha halpha0 halpha1 hsmall m le_rfl
  have haeCaps := hcapsprod M hregCaps (stepOneDelta C1 alpha) hdeltamem
    hfact.floorEight hsmall
  filter_upwards [haeOsc, haeCaps] with omega hOsc hCap
  intro n L hnm hmL hpay u h g Kg Kh hsol hgHol hhHol hsup hgradh x hx hgate
  have hKg : (0 : ℝ) ≤ Kg := holderHalf_const_nonneg hgHol
  have hKh : (0 : ℝ) ≤ Kh := holderHalf_const_nonneg hhHol
  have hv : offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
    offGridLatticeIndex_mem_of_mem_cube n hx
  have hoscfun := hOsc L n (offGridLatticeIndex n x) hmL hpay.2.1 hv hpay u h g Kg Kh
    hKg hKh hsol hgHol hhHol hsup hgradh
  set CBraw : ℝ :=
    2 * (d : ℝ) * ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 + 1) with hCBrawDef
  have hCBraw0 : (0 : ℝ) ≤ CBraw := by
    have hsq : (0 : ℝ) ≤ (Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 := sq_nonneg _
    have hdd : (0 : ℝ) ≤ 2 * (d : ℝ) := by
      have hcd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hcd]
    rw [hCBrawDef]
    exact mul_nonneg hdd (by linarith only [hsq])
  have hCBle : CBraw ≤ CBu := by
    rw [hCBrawDef, hCBuDef]
    exact capsConst_le_rootClauseBCapsUniform d hCcaps.le hdeltamem.2
  have hCWGle : edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS ≤ CWGu := by
    rw [hCWGuDef]
    exact mul_le_mul_of_nonneg_right
      (edFinalDataOscW_le_uniform hfact.ltHalf hfact.leQuarter hCbd)
      (stepFourGagliardoConst_nonneg d _)
  have hCWG0 : (0 : ℝ) ≤ edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hfact.ltHalf hCbd)
      (stepFourGagliardoConst_nonneg d _)
  have hstep1 := rootClauseBBoundaryPrefactor_mono_ccacc d (Cch := Cch)
    (Cosc := Cosc) (CBc := CBraw) (CB := CBraw)
    (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
    (CWG := edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS)
    (CWH := boundaryCWH d Cb C kb) (CdM := rootClauseBDataMConst d CBraw) hCch.le hCosc
    hCBraw0 (rootClauseBTopCtr_nonneg d _) hCWG0 hCWH
    (rootClauseBDataMConst_nonneg d CBraw)
    (rootClauseBCaccUniform_mono Cc hCBraw0 hCBle)
  have hstep2 := rootClauseBBoundaryPrefactor_mono_data d (Cch := Cch)
    (Ccacc := rootClauseBCaccUniform Cc CBu) (Cosc := Cosc) (CBc := CBraw)
    (CBc' := CBu) (CB := CBraw) (CB' := CBu)
    (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
    (CWG := edFinalDataOscW M (edBoundaryCbd d Cb C kb) *
      stepFourGagliardoConst d stepOneS) (CWG' := CWGu)
    (CWH := boundaryCWH d Cb C kb) (CWH' := boundaryCWH d Cb C kb)
    (CdM := rootClauseBDataMConst d CBraw) (CdM' := rootClauseBDataMConst d CBu)
    hCch.le (rootClauseBCaccUniform_nonneg Cc CBu) hCosc hCBraw0
    (rootClauseBTopCtr_nonneg d _) hCWG0 hCWH (rootClauseBDataMConst_nonneg d CBraw)
    hCBle hCBle hCWGle (le_refl _) (rootClauseBDataMConst_mono d hCBle)
  exact hend M m Ecap (hstate m) hfact.ltHalf L Cb C kb omega u h le_rfl hnm hmL
    (fun k' n0 v0 hgood L' hL' => hCap k' n0 v0 hgood L' hL') hpay hx hgate hsol hgHol
    hKg hKh hCBraw0 hC.le hCosc (two_mul_dim_le_stepOneC1 d Cedos 1 Citer (kb + 1))
    halpha0.le (le_of_lt halpha1) hoscfun (le_trans hstep1 hstep2)

end

end Algsuperdiff.Section4.Provider.Regularity
