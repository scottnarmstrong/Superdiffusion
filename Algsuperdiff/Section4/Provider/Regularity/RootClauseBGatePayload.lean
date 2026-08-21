/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateChain
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseAssembly

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The payload endpoint at the caller's own coarse gate -/

/-- **Clause (B) of `RootAssemblyConditional.RootLatticeDisplay`, at the re-cut
coarse scale and at `(GATE k_c)`.**

`RootClauseBClosePayload.rootClauseB_display_offGrid_freeUniform` with the
printed guard replaced by the strictly weaker cube gate at the coarse scale. -/
theorem rootClauseB_display_offGrid_gate_freeUniform (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {alpha : ℝ} {n m kc n' : ℤ} {x : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d}
          {Khol Kd CB CBc Cdel Cosc CdM C1 delta Cest : ℝ} {B : ℕ},
          m ≤ m0 → n' ≤ m - 1 → n + 1 ≤ n' - 2 → n ≤ m →
          n' ≤ kc → kc ≤ m - 1 → m - (kc + 1) ≤ (B : ℤ) + 1 →
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
          RootClauseBTopPayload M L Khol Kd CB CBc Cdel Cosc CdM alpha n m kc n' x
            omega uglob gsrc →
          rootClauseBPrefactor d Cch (rootClauseBCaccUniform Cc CBc)
              Cosc CBc CB (rootClauseBTopCtr d Kd)
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS) CdM ≤
            Cest →
          ((fun y => offGridCentre n x + y) '' openCubeSet (originCube d kc) ⊆
              openCubeSet (originCube d m) →
            Real.sqrt M.nu *
                Support.normalizedL2On
                  (truncatedWindow (offGridCentre n x) m (n + 1))
                  (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
              ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                (Real.sqrt M.nu *
                    Support.normalizedL2On (openCubeSet (originCube d m))
                      (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                  Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                    Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) := by
  obtain ⟨Cch, Cc, hCch, hCc, hmain⟩ := rootClauseB_display_gate_freeCoarse d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L alpha n m kc n' x omega uglob hdat gsrc Khol Kd CB CBc Cdel
    Cosc CdM C1 delta Cest B hmm0 hn' hcore hnm hn'kc hkc hgapTop hsol hgL2 hgW hKhol hKd
    hCB hCBc hCdel hCosc hCdM hC1 halpha0 halpha1 hdelta hgap hbudget hpay hCest hgate
  refine hmain M m0 Ecap hS hgamma L omega uglob hdat hgate hmm0 hn' hcore hnm hn'kc hkc
    hgapTop hsol hgL2 hgW hKhol hKd hCB hCBc hCdel hCosc hCdM hC1 halpha0 halpha1 hdelta
    hgap hbudget hpay.caps hpay.capsCacc hpay.dataB hpay.dataM hpay.osc ?_
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M (n' + 1) : ℝ) :=
    (Annealed.sigmaBar M (n' + 1)).2
  have hcacc := stepSevenCaccConst_le_uniform (k := n') hCc hsigma hpay.capsCacc
  have hCtr : (0 : ℝ) ≤ rootClauseBTopCtr d Kd := rootClauseBTopCtr_nonneg d Kd
  have hCWG : (0 : ℝ) ≤ edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS :=
    mul_nonneg (edFinalDataOscW_nonneg hgamma hCdel) (stepFourGagliardoConst_nonneg d _)
  exact le_trans (rootClauseBPrefactor_mono_ccacc d hCch.le hCosc hCB hCtr hCWG hCdM
    hcacc) hCest

/-! ## 2. The payload, produced at the gate -/

/-- **The five payload fields at `(GATE m-2)`.**

`RootClauseBCloseAssembly.exists_rootClauseBTopPayload` with the printed
interiority replaced by the gate at `m-2`, which the joint pigeonhole's own
bound `k ≤ m-1` (hence `k_c ≤ m-2`) makes sufficient for both produced fields.
The returned `k_c ≤ m-2` is the parent's `k_c ≤ m-1` sharpened — the extra unit
is exactly what lets a consumer descend the gate. -/
theorem exists_rootClauseBTopPayload_gate [NeZero d] {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {C1 alpha Khol CB Cdel Cosc : ℝ} {n m L : ℤ}
    {x : Vec d} {omega : Cutoff.CutoffSample d}
    {uglob : H1Function (openCubeSet (originCube d m))} {gsrc : Vec d → Vec d}
    (hmerge : ∀ (k n0 : ℤ) (v0 : Fin d → ℤ),
      omega ∈ stepThreeGoodEvent M (stepOneDelta C1 alpha) k
          (Support.triadicLatticePoint n0 v0) →
        ∀ L' : ℤ, k ≤ L' →
          StepSevenLambdaCaps (originCube d k)
            (Support.fluxCorrectedCoeffFamily M L' k (originCube d k)
              (Cutoff.translateCutoffSample
                (Support.triadicLatticePoint n0 v0) omega))
            ((Annealed.sigmaBar M k : ℝ)) CB)
    (hwin : RootWindowPayload M C1 alpha n m omega)
    (hx : x ∈ openCubeSet (originCube d m))
    (hgate : (fun y => offGridCentre n x + y) '' openCubeSet (originCube d (m - 2)) ⊆
      openCubeSet (originCube d m))
    (hmL : m ≤ L) (hmm0 : m ≤ m0) (hKhol : 0 ≤ Khol) (hCB : 0 ≤ CB)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
    (hosc : ∀ n' kc : ℤ, n ≤ n' → n' ≤ kc → kc ≤ m →
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
            (edFinalDataG M Cdel
              (Khol * stepFourGagliardoConst d stepOneS) m + 0)) :
    ∃ (kc n' : ℤ) (B : ℕ),
      n' ≤ m - 1 ∧ n + 1 ≤ n' - 2 ∧ n' ≤ kc ∧ kc ≤ m - 2 ∧
        m - (kc + 1) ≤ (B : ℤ) + 1 ∧ n' - n ≤ (B : ℤ) + 6 ∧
        (B : ℝ) ≤ stepOneDelta C1 alpha * (((m - n).toNat : ℝ) + 1) ∧
        RootClauseBTopPayload M L Khol (rootClauseBDataBConst d) CB CB Cdel Cosc
          (rootClauseBDataMConst d CB) alpha n m kc n' x omega uglob gsrc := by
  obtain ⟨-, -, hbudget, -⟩ := hwin
  have hv : offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
    offGridLatticeIndex_mem_of_mem_cube n hx
  have hcard := (hbudget _ hv).2.2.1
  obtain ⟨j, k, hjlo, hjk, hkhi, hgapLo, hgapHi, hcapsj, hcapsk⟩ :=
    exists_rootClauseBCapsPair hmerge hbudget hv hmL
  obtain ⟨kc, rfl⟩ : ∃ kc : ℤ, k = kc + 1 := ⟨k - 1, by ring⟩
  obtain ⟨n', rfl⟩ : ∃ n' : ℤ, j = n' + 1 := ⟨j - 1, by ring⟩
  have hgateKc : (fun y => offGridCentre n x + y) '' openCubeSet (originCube d kc) ⊆
      openCubeSet (originCube d m) :=
    image_add_subset_openCubeSet_of_gate_le (by omega) hgate
  have hgateN : (fun y => offGridCentre n x + y) '' openCubeSet (originCube d n') ⊆
      openCubeSet (originCube d m) :=
    image_add_subset_openCubeSet_of_gate_le (by omega) hgate
  refine ⟨kc, n',
    (stepThreeBadSet M (stepOneDelta C1 alpha) n m
      (Support.triadicLatticePoint n (offGridLatticeIndex n x)) omega).card,
    by omega, by omega, by omega, by omega, by omega, by omega, hcard, ?_⟩
  exact
    { caps := hcapsk
      capsCacc := hcapsj
      dataB := rootClauseB_dataB_gate hgateKc (by omega) hKhol hgHol hgL2 hgW
      dataM := rootClauseB_dataM_gate hS hgamma hmm0 (by omega) hgateN hKhol hCB hgHol
        hgL2 hgW hcapsj
      osc := hosc n' kc (by omega) (by omega) (by omega) }

/-! ## 3. Clause (B) at the gate, from `RootWindowPayload` and `hosc` alone -/

/-- **The clause-(B) endpoint at the root's own inputs, at `(GATE m-2)`.**

`RootClauseBCloseAssembly.rootClauseB_display_offGrid_of_windowPayload` with
the printed guard replaced by the gate at `m-2`. -/
theorem rootClauseB_display_offGrid_gate_of_windowPayload (d : ℕ) [NeZero d] :
    ∃ Cch Cc : ℝ, 0 < Cch ∧ 0 < Cc ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        ∀ (L : ℤ) {C1 alpha : ℝ} {n m : ℤ} {x : Vec d}
          (omega : Cutoff.CutoffSample d)
          (uglob hdat : H1Function (openCubeSet (originCube d m)))
          {gsrc : Vec d → Vec d} {Khol CB Cdel Cosc Cest : ℝ},
          m ≤ m0 → n ≤ m → m ≤ L →
          (∀ (k n0 : ℤ) (v0 : Fin d → ℤ),
            omega ∈ stepThreeGoodEvent M (stepOneDelta C1 alpha) k
                (Support.triadicLatticePoint n0 v0) →
              ∀ L' : ℤ, k ≤ L' →
                StepSevenLambdaCaps (originCube d k)
                  (Support.fluxCorrectedCoeffFamily M L' k (originCube d k)
                    (Cutoff.translateCutoffSample
                      (Support.triadicLatticePoint n0 v0) omega))
                  ((Annealed.sigmaBar M k : ℝ)) CB) →
          RootWindowPayload M C1 alpha n m omega →
          x ∈ openCubeSet (originCube d m) →
          (fun y => offGridCentre n x + y) '' openCubeSet (originCube d (m - 2)) ⊆
            openCubeSet (originCube d m) →
          Support.IsDirichletSolutionOn
              (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
              (originCube d m) uglob hdat gsrc →
          Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
              (1 / 2) Khol gsrc →
          0 ≤ Khol → 0 ≤ CB → 0 ≤ Cdel → 0 ≤ Cosc →
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
                  (edFinalDataG M Cdel
                    (Khol * stepFourGagliardoConst d stepOneS) m + 0)) →
          rootClauseBPrefactor d Cch (rootClauseBCaccUniform Cc CB)
              Cosc CB CB (rootClauseBTopCtr d (rootClauseBDataBConst d))
              (edFinalDataOscW M Cdel * stepFourGagliardoConst d stepOneS)
              (rootClauseBDataMConst d CB) ≤ Cest →
          Real.sqrt M.nu *
              Support.normalizedL2On
                (truncatedWindow (offGridCentre n x) m (n + 1))
                (fun y => Real.sqrt (vecNormSq (uglob.grad y)))
            ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (Real.sqrt M.nu *
                  Support.normalizedL2On (openCubeSet (originCube d m))
                    (fun y => Real.sqrt (vecNormSq (uglob.grad y))) +
                Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol) := by
  obtain ⟨Cch, Cc, hCch, hCc, hmain⟩ := rootClauseB_display_offGrid_gate_freeUniform d
  refine ⟨Cch, Cc, hCch, hCc, ?_⟩
  intro M m0 Ecap hS hgamma L C1 alpha n m x omega uglob hdat gsrc Khol CB Cdel Cosc
    Cest hmm0 hnm hmL hmerge hwin hx hgate hsol hgHol hKhol hCB hCdel hCosc hC1
    halpha0 halpha1 hosc hCest
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  obtain ⟨hgL2, hgW⟩ := memLp_pair_of_holderHalf hd hKhol hgHol
  obtain ⟨kc, n', B, hn', hcore, hn'kc, hkc, hgapTop, hgap, hbudget, hpay⟩ :=
    exists_rootClauseBTopPayload_gate hS hgamma hmerge hwin hx hgate hmL hmm0 hKhol hCB
      hgHol hgL2 hgW hosc
  exact hmain M m0 Ecap hS hgamma L omega uglob hdat hmm0 hn' hcore hnm hn'kc (by omega)
    hgapTop hsol hgL2 hgW hKhol (rootClauseBDataBConst_nonneg d) hCB hCB hCdel hCosc
    (rootClauseBDataMConst_nonneg d CB) hC1 halpha0 halpha1 (le_refl _) hgap hbudget
    hpay hCest (image_add_subset_openCubeSet_of_gate_le (by omega) hgate)

end

end Algsuperdiff.Section4.Provider.Regularity
