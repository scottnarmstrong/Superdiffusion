/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalOsc
import Algsuperdiff.Section4.Provider.GoodEvents.InductionState

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Two missing monotonicity steps in the `C_B` slot -/

/-- `rootClauseBDataMConst` is monotone in its `C_Bc` slot. -/
theorem rootClauseBDataMConst_mono (d : ℕ) {CBc CBc' : ℝ} (h : CBc ≤ CBc') :
    rootClauseBDataMConst d CBc ≤ rootClauseBDataMConst d CBc' := by
  have hF : (0 : ℝ) ≤ stepSevenCaccForcingFactor := stepSevenCaccForcingFactor_nonneg
  have hstep : 4 * stepSevenCaccForcingFactor * (64 / 7 * CBc) ≤
      4 * stepSevenCaccForcingFactor * (64 / 7 * CBc') := by
    refine mul_le_mul_of_nonneg_left (by linarith only [h]) ?_
    linarith only [hF]
  rw [rootClauseBDataMConst, rootClauseBDataMConst]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hstep)
    (rootClauseBDataBConst_nonneg d)

/-- `rootClauseBCaccUniform` is monotone in its `C_B` slot. -/
theorem rootClauseBCaccUniform_mono (C : ℝ) {CB CB' : ℝ} (hCB : 0 ≤ CB)
    (h : CB ≤ CB') : rootClauseBCaccUniform C CB ≤ rootClauseBCaccUniform C CB' := by
  have hsq : CB ^ (2 : ℕ) ≤ CB' ^ (2 : ℕ) := pow_le_pow_left₀ hCB h 2
  have h1 : (16384 : ℝ) / 441 * CB ^ (2 : ℕ) ≤ 16384 / 441 * CB' ^ (2 : ℕ) := by
    linarith only [hsq]
  have h10 : (0 : ℝ) ≤ 16384 / 441 * CB ^ (2 : ℕ) := by
    have := pow_nonneg hCB 2
    linarith only [this]
  have h2 : (16384 / 441 * CB ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      (16384 / 441 * CB' ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ h10 h1 2
  have hcoef : (0 : ℝ) ≤ (2 * max 1 C) ^ (4 : ℕ) * 4 := by
    have hm : (1 : ℝ) ≤ max 1 C := le_max_left _ _
    have : (0 : ℝ) ≤ (2 * max 1 C) ^ (4 : ℕ) := by
      refine pow_nonneg ?_ 4
      linarith only [hm]
    linarith only [this]
  rw [rootClauseBCaccUniform, rootClauseBCaccUniform]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h2 hcoef)

/-! ## 1b. The Hölder constants are nonnegative -/

/-- **`0 ≤ K` is not a hypothesis, it is a consequence.**

The frozen root prints `HolderSeminormBoundOn (□_m) (1/2) K f` and no sign
condition on `K`; every §4.4 producer nevertheless binds `0 ≤ K`.  The binder
is redundant: the open cube contains `0` and the point `(3^m/4)·𝟙`, whose
distance is positive, so `0 ≤ ‖f y - f 0‖ ≤ K‖y‖^{1/2}` forces `0 ≤ K`. -/
theorem holderHalf_const_nonneg [NeZero d] {m : ℤ} {K : ℝ} {f : Vec d → Vec d}
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    0 ≤ K := by
  classical
  obtain ⟨i0⟩ : Nonempty (Fin d) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne d))
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hymem : (fun _ : Fin d => (3 : ℝ) ^ m / 4) ∈ openCubeSet (originCube d m) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    refine ⟨?_, ?_⟩
    · show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (3 : ℝ) ^ m / 4
      linarith only [h3]
    · show (3 : ℝ) ^ m / 4 < (1 / 2 : ℝ) * (3 : ℝ) ^ m
      linarith only [h3]
  have h0mem : (0 : Vec d) ∈ openCubeSet (originCube d m) :=
    zero_mem_openCubeSet_originCube d m
  have hbound := hf _ hymem 0 h0mem
  have hnormpos : (0 : ℝ) < ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ := by
    have hi : ‖((fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)) i0‖ ≤
        ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ := norm_le_pi_norm _ i0
    have hval : ‖((fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)) i0‖ =
        (3 : ℝ) ^ m / 4 := by
      show ‖(3 : ℝ) ^ m / 4 - 0‖ = (3 : ℝ) ^ m / 4
      rw [sub_zero, Real.norm_eq_abs, abs_of_pos (by linarith only [h3])]
    rw [hval] at hi
    linarith only [hi, h3]
  have hp : (0 : ℝ) <
      ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hnormpos _
  by_contra hK
  push_neg at hK
  have hneg : K * ‖(fun _ : Fin d => (3 : ℝ) ^ m / 4) - (0 : Vec d)‖ ^ (1 / 2 : ℝ) < 0 :=
    mul_neg_of_neg_of_pos hK hp
  have hnn : (0 : ℝ) ≤ ‖f (fun _ : Fin d => (3 : ℝ) ^ m / 4) - f 0‖ := norm_nonneg _
  linarith only [hbound, hneg, hnn]

/-! ## 2. The endpoint -/

/-- **Clause (B) of `RootAssemblyConditional.RootLatticeDisplay`, produced.**

The interior-guarded, boundary-leg-free half of the root's lattice-centre
display, almost surely, at a `C_est` fixed before the model and the sample are
chosen. -/
theorem rootClauseB_display_offGrid_final (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cedos Cannp Citer Cest gamma0 : ℝ) (k : ℕ),
      1 ≤ Cedos ∧ 0 < Cannp ∧ 0 ≤ Cest ∧ 0 < gamma0 ∧ 11 ≤ k ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
          ∀ m : ℤ,
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ n L : ℤ, n ≤ m → m ≤ L →
                RootWindowPayload M (stepOneC1 d Cedos Cannp Citer k) alpha n m
                    omega →
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
                      (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
                        Real.sqrt M.nu *
                            Support.normalizedL2On
                              (truncatedWindow (offGridCentre n x) m (n + 1))
                              (fun y => Real.sqrt (vecNormSq (u.grad y)))
                          ≤ Cest *
                              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                            (Real.sqrt M.nu *
                                Support.normalizedL2On (openCubeSet (originCube d m))
                                  (fun y => Real.sqrt (vecNormSq (u.grad y))) +
                              Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)) := by
  classical
  obtain ⟨C, Cann, Citer, Cosc, Cdel, k, hC, hCann, hCosc, hCdel, hk11, hoscprod⟩ :=
    exists_rootClauseBOsc d hd
  obtain ⟨Ccaps, hCcaps, hcapsprod⟩ := ae_stepSevenLambdaCaps_merged d
  obtain ⟨Cind, hCind6, -, hind⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d 0
  obtain ⟨Cch, Cc, hCch, hCc, hend⟩ := rootClauseB_display_offGrid_of_windowPayload d
  have hCindpos : (0 : ℝ) < Cind := by linarith only [hCind6]
  have hCmax : (0 : ℝ) < max C Ccaps := lt_of_lt_of_le hC (le_max_left _ _)
  set Cedos : ℝ := rootClauseBFundCedos d C Cann k with hCedosDef
  set C1 : ℝ := stepOneC1 d Cedos 1 Citer k with hC1Def
  have hC1two : (2 : ℝ) ≤ C1 := two_le_stepOneC1 d Cedos 1 Citer k
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hC1two]
  obtain ⟨gamma0, hgamma0, hfacts⟩ :=
    exists_rootClauseBGammaFacts d (C := max C Ccaps) (Cann := Cann) (Cind := Cind)
      (C1 := C1) (Crg := Crg) hcstar hCmax hCann hCindpos hC1pos hCrg
  set CBu : ℝ := rootClauseBCapsUniform d Ccaps with hCBuDef
  have hCBu : (0 : ℝ) ≤ CBu := rootClauseBCapsUniform_nonneg d Ccaps
  set CWGu : ℝ := rootClauseBOscWUniform Cdel * stepFourGagliardoConst d stepOneS
    with hCWGuDef
  refine ⟨Cedos, 1, Citer,
    rootClauseBPrefactor d Cch (rootClauseBCaccUniform Cc CBu) Cosc CBu CBu
      (rootClauseBTopCtr d (rootClauseBDataBConst d)) CWGu
      (rootClauseBDataMConst d CBu),
    gamma0, k, one_le_rootClauseBFundCedos d C Cann k, one_pos, ?_, hgamma0, hk11, ?_⟩
  · -- `0 ≤ C_est`
    have hCWGu0 : (0 : ℝ) ≤ CWGu := by
      rw [hCWGuDef]
      exact mul_nonneg (rootClauseBOscWUniform_nonneg hCdel)
        (stepFourGagliardoConst_nonneg d _)
    have hzero := rootClauseBPrefactor_mono_data d (Cch := Cch)
      (Ccacc := rootClauseBCaccUniform Cc CBu) (Cosc := Cosc) (CBc := 0) (CBc' := CBu)
      (CB := 0) (CB' := CBu) (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
      (CWG := 0) (CWG' := CWGu) (CdM := 0) (CdM' := rootClauseBDataMConst d CBu)
      hCch.le (rootClauseBCaccUniform_nonneg Cc CBu) hCosc le_rfl
      (rootClauseBTopCtr_nonneg d _) le_rfl le_rfl hCBu hCBu hCWGu0
      (rootClauseBDataMConst_nonneg d CBu)
    refine le_trans ?_ hzero
    rw [rootClauseBPrefactor]
    have hCg : (0 : ℝ) ≤ rootClauseBCg d (rootClauseBCaccUniform Cc CBu) Cosc 0 :=
      rootClauseBCg_nonneg d (rootClauseBCaccUniform_nonneg Cc CBu) hCosc
    have hX : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * 0) + 32 / 7 * 0)) *
        rootClauseBTopCtr d (rootClauseBDataBConst d) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) ?_)
        (rootClauseBTopCtr_nonneg d _)
      have h0 : (0 : ℝ) ≤ Real.sqrt (32 / 7 * 0) + 32 / 7 * 0 := by
        have := Real.sqrt_nonneg ((32 : ℝ) / 7 * 0)
        linarith only [this]
      exact mul_nonneg (by linarith only [hCch]) h0
    have hL : (0 : ℝ) ≤ rootClauseBCg d (rootClauseBCaccUniform Cc CBu) Cosc 0 *
        Real.sqrt 4 * (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
          stepSevenBridgeConst stepSevenCgS *
          (Cch * 64 * (Real.sqrt (32 / 7 * 0) + 32 / 7 * 0)) *
          rootClauseBTopCtr d (rootClauseBDataBConst d)) :=
      mul_nonneg (mul_nonneg hCg (Real.sqrt_nonneg 4)) hX
    have hR : (0 : ℝ) ≤ rootClauseBCg d (rootClauseBCaccUniform Cc CBu) Cosc 0 *
        (Real.sqrt 4 * 0 + 0) := by
      rw [mul_zero, add_zero, mul_zero]
    linarith only [hL, hR]
  intro M hcs hgammale alpha halpha0 halpha m
  have hfact := hfacts M hcs hgammale
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsqrtpos : (0 : ℝ) < Crg * Real.sqrt M.gamma :=
    mul_pos hCrg (Real.sqrt_pos.mpr hg0)
  have halpha1 : alpha < 1 := by linarith only [halpha, hsqrtpos]
  have hcs10 : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) :=
    pow_nonneg ((Disorder.cstar_characterization M).1).le 10
  have hinvC : (max C Ccaps)⁻¹ ≤ C⁻¹ := inv_anti₀ hC (le_max_left _ _)
  have hinvCaps : (max C Ccaps)⁻¹ ≤ Ccaps⁻¹ := inv_anti₀ hCcaps (le_max_right _ _)
  have hregC : M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right hinvC hcs10)
  have hregCaps : M.gamma ≤ Ccaps⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC (mul_le_mul_of_nonneg_right hinvCaps hcs10)
  have hfree : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
        (C⁻¹ * stepOneS ^ (4 : ℕ)) := by
    refine le_trans hfact.smallFree (mul_le_mul_of_nonneg_left ?_ ?_)
    · exact mul_le_mul_of_nonneg_right hinvC (pow_nonneg (by rw [stepOneS]; norm_num) 4)
    · exact mul_nonneg (Real.rpow_pos_of_pos (by rw [stepOneS]; norm_num) _).le
        (pow_nonneg ((Disorder.cstar_characterization M).1).le 2)
  have hsmall := hfact.smallEp alpha halpha0 halpha
  obtain ⟨Ecap, -, -, hstate⟩ := hind M hfact.regimeInd
  have hdeltamem := stepOneDelta_mem hC1two halpha0 halpha1
  have haeOsc := hoscprod M m Ecap (hstate m) hfact.ltHalf hregC hfact.regimeAnn
    hfact.le256 hfree alpha halpha0 halpha1 hsmall m le_rfl
  have haeCaps := hcapsprod M hregCaps (stepOneDelta C1 alpha) hdeltamem
    hfact.floorEight hsmall
  filter_upwards [haeOsc, haeCaps] with omega hOsc hCap
  intro n L hnm hmL hpay u h g Kg Kh hsol hgHol hhHol x hx hzin
  have hKg : (0 : ℝ) ≤ Kg := holderHalf_const_nonneg hgHol
  have hKh : (0 : ℝ) ≤ Kh := holderHalf_const_nonneg hhHol
  have hv : offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
    offGridLatticeIndex_mem_of_mem_cube n hx
  have hoscfun := hOsc L n (offGridLatticeIndex n x) hmL hpay.2.1 hv hzin hpay u h g
    Kg Kh hKg hKh hsol hgHol hhHol
  set CBraw : ℝ :=
    2 * (d : ℝ) * ((Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 + 1) with hCBrawDef
  have hCBraw0 : (0 : ℝ) ≤ CBraw := by
    have hsq : (0 : ℝ) ≤ (Ccaps * stepOneEp (stepOneDelta C1 alpha)) ^ 2 := sq_nonneg _
    have hdd : (0 : ℝ) ≤ 2 * (d : ℝ) := by
      have hc : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hc]
    rw [hCBrawDef]
    exact mul_nonneg hdd (by linarith only [hsq])
  have hCBle : CBraw ≤ CBu := by
    rw [hCBrawDef, hCBuDef]
    exact capsConst_le_rootClauseBCapsUniform d hCcaps.le hdeltamem.2
  have hCWGle : edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS ≤ CWGu := by
    rw [hCWGuDef]
    exact mul_le_mul_of_nonneg_right
      (edFinalDataOscW_le_uniform hfact.ltHalf hfact.leQuarter hCdel)
      (stepFourGagliardoConst_nonneg d _)
  have hCWG0 : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hfact.ltHalf hCdel)
      (stepFourGagliardoConst_nonneg d _)
  have hstep1 := rootClauseBPrefactor_mono_ccacc d (Cch := Cch)
    (Cosc := Cosc) (CBc := CBraw) (CB := CBraw)
    (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
    (CWG := edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS)
    (CdM := rootClauseBDataMConst d CBraw) hCch.le hCosc hCBraw0
    (rootClauseBTopCtr_nonneg d _) hCWG0 (rootClauseBDataMConst_nonneg d CBraw)
    (rootClauseBCaccUniform_mono Cc hCBraw0 hCBle)
  have hstep2 := rootClauseBPrefactor_mono_data d (Cch := Cch)
    (Ccacc := rootClauseBCaccUniform Cc CBu) (Cosc := Cosc) (CBc := CBraw)
    (CBc' := CBu) (CB := CBraw) (CB' := CBu)
    (Ctr := rootClauseBTopCtr d (rootClauseBDataBConst d))
    (CWG := edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) (CWG' := CWGu)
    (CdM := rootClauseBDataMConst d CBraw) (CdM' := rootClauseBDataMConst d CBu)
    hCch.le (rootClauseBCaccUniform_nonneg Cc CBu) hCosc hCBraw0
    (rootClauseBTopCtr_nonneg d _) hCWG0 (rootClauseBDataMConst_nonneg d CBraw)
    hCBle hCBle hCWGle (rootClauseBDataMConst_mono d hCBle)
  refine hend M m Ecap (hstate m) hfact.ltHalf L omega u h le_rfl hnm hmL
    (fun k' n0 v0 hgood L' hL' => hCap k' n0 v0 hgood L' hL') hpay hx hzin hsol hgHol
    hKg hCBraw0 hCdel hCosc (two_mul_dim_le_stepOneC1 d Cedos 1 Citer k)
    halpha0.le (le_of_lt halpha1) hoscfun (le_trans hstep1 hstep2) hzin

end

end Algsuperdiff.Section4.Provider.Regularity
