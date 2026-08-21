/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseAEndpoint
import Algsuperdiff.Section4.Support.ClassicalGradient

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The boundary half of clause (A) at the frozen binder block -/

/-- **Clause (A) of the a.e. lattice display at the boundary centres, frozen
binders.**

`RootClauseABoundary.RootDisplayClauseABoundaryAe`'s body, character for
character, with the root's two printed datum binders — the scale-weighted sup
bound on `∇h` and the classical `C¹` tie `Support.HasGradientOn` — inserted in
the root's own order. -/
def RootDisplayClauseABoundaryC1Ae (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
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
              (∀ y ∈ openCubeSet (originCube d m),
                ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
              Support.HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (offGridCentre n x ∉ openCubeSet (originCube d (m - 1)) →
                  Real.sqrt M.nu *
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
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))

/-- **`RootDisplayClauseABoundaryAe` implies the frozen-binder form.**  Two
extra hypotheses are introduced and discarded. -/
theorem RootDisplayClauseABoundaryC1Ae_of_boundary {M : ABKModel d} {C1 Cest alpha : ℝ}
    (h : RootDisplayClauseABoundaryAe M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1Ae M C1 Cest alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh _hsup _hgradh x hx hout
  exact h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hout

/-- The printed Hölder binder on `□_m` forces its constant nonnegative: `□_m` has
two distinct points. -/
private theorem holderHalfConst_nonneg_c1 [NeZero d] {m : ℤ} {K : ℝ}
    {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    (hK : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    (0 : ℝ) ≤ K := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hx0 : (0 : Vec d) ∈ openCubeSet (originCube d m) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (0 : ℝ) ∧ (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m
    exact ⟨by linarith only [h3], by linarith only [h3]⟩
  have hy0 : (fun _ => (1 / 4 : ℝ) * (3 : ℝ) ^ m : Vec d) ∈
      openCubeSet (originCube d m) := by
    rw [mem_openCubeSet_originCube_iff]
    exact fun _ => ⟨by linarith only [h3], by linarith only [h3]⟩
  refine hK.nonneg hx0 hy0 ?_
  intro hEq
  have hi := congrFun hEq (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)
  simp only [Pi.zero_apply] at hi
  linarith only [hi, h3]

theorem RootDisplayClauseABoundaryC1Ae.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseABoundaryC1Ae M C1 Cest alpha) :
    RootDisplayClauseABoundaryC1Ae M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh hsup hgradh x hx hout
  have hB0 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
      + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    have hL2 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y))) :=
      mul_nonneg (Real.sqrt_nonneg _) (Support.normalizedL2On_nonneg _ _)
    have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hKg0 : (0 : ℝ) ≤ Kg := holderHalfConst_nonneg_c1 hKg
    have hKh0 : (0 : ℝ) ≤ Kh := holderHalfConst_nonneg_c1 hKh
    have hGleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKg0
    have hHleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ) *
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKh0
    linarith only [hL2, hGleg, hHleg]
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hrpow) hB0)

/-! ## 2. The endpoint: the frozen root at ONE named boundary conditional -/

/-- The frozen root's entire conclusion — the `∃ γ₀ C` block, the `(M, α, m)`
binders, the minimal scale with its measurability and tail, and the a.e.
two-clause energy-density estimate with both extra binders in place — produced
from the unconditional clause-(B) endpoint and one named conditional: the
boundary-centre clause (A) at the frozen binder block, asked at whatever `C₁` the
clause-(B) chain pins and at the producer's own `(C_est, γ₀, C_rg)`.

`hbdry` is a carried mathematical obligation, NOT a source premise: it is the
printed estimate itself at the centres `offGridCentre n x ∉ □_{m-1}`. -/
theorem anomalous_regularity_provider_of_boundaryClauseAC1 (d : ℕ) [NeZero d]
    (hd : d ≠ 0) (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg)
    (hbdry : ∀ (Cedos Cannp Citer : ℝ) (k : ℕ), 1 ≤ Cedos → 0 < Cannp → 11 ≤ k →
      ∃ CestA gamma0A CrgA : ℝ, 0 ≤ CestA ∧ 0 < gamma0A ∧ 0 < CrgA ∧
        ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0A →
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - CrgA * Real.sqrt M.gamma →
            RootDisplayClauseABoundaryC1Ae M
              (stepOneC1 d Cedos Cannp Citer k) CestA alpha) :
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
                  Support.HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
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
  obtain ⟨Cedos, Cannp, Citer, CestB, gamma0B, k, hCedos, hCannp, hCestB, hgamma0B,
    hk11, hB⟩ := clauseB_endpoint_as_clauseBAe d hd cstar Crg hcstar hCrg
  obtain ⟨CestA, gamma0A, CrgA, hCestA, hgamma0A, hCrgA, hA⟩ :=
    hbdry Cedos Cannp Citer k hCedos hCannp hk11
  obtain ⟨gamma0, C0, hg0pos, hC0pos, -, -, -, hpkg⟩ :=
    rootAssembly_aePackage d cstar hcstar Cedos Citer Cannp k hk11
  have hCest : (0 : ℝ) ≤ max CestB CestA := le_trans hCestB (le_max_left _ _)
  refine ⟨min gamma0 (min gamma0B gamma0A),
    max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA),
    lt_min hg0pos (lt_min hgamma0B hgamma0A),
    lt_of_lt_of_le hCrg (le_trans (le_max_left _ _) (le_max_right _ _)), ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hC0le : C0 ≤ max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCestle : (3 : ℝ) ^ d * max CestB CestA ≤
      max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have halphaC0 : alpha ≤ 1 - C0 * Real.sqrt M.gamma :=
    alphaRange_of_mono_const hC0le halpha
  have halphaB : alpha ≤ 1 - Crg * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_trans (le_max_left _ _) (le_max_right _ _)) halpha
  have halphaA : alpha ≤ 1 - CrgA * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_trans (le_max_right _ _) (le_max_right _ _)) halpha
  obtain ⟨Z, hXmeas, hXtail, hae⟩ :=
    hpkg M hcs (rootGamma0_le_left hgamma) alpha halpha0 halphaC0 m
  refine ⟨minimalScaleX Z k, hXmeas, ?_, ?_⟩
  · intro N
    exact le_trans (hXtail N)
      (minimalScaleTail_ofReal_mono_const hC0pos hC0le hgpos)
  have hBm := ((hB M hcs (rootGamma0_le_left (rootGamma0_le_right hgamma)) alpha halpha0
    halphaB).mono_const (le_max_left CestB CestA)) m
  have hAm := ((hA M hcs (rootGamma0_le_right (rootGamma0_le_right hgamma)) alpha halpha0
    halphaA).mono_const (le_max_right CestB CestA)) m
  filter_upwards [hae, hBm, hAm] with omega hpay hdispB hdispA
  intro L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx n hn hgate
  have hpayn := hpay n hn hgate
  have hclB := hdispB n hn hpayn L hL u h g Kg Kh hdir hKg hKh x hx
  have hclA : Real.sqrt M.nu *
        Support.normalizedL2On
          (truncatedWindow (offGridCentre n x) m (n + 1))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      ≤ max CestB CestA *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
        (Real.sqrt M.nu *
            Support.normalizedL2On (openCubeSet (originCube d m))
              (fun y => Real.sqrt (vecNormSq (u.grad y)))
          + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
              Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
          + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
              Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
    by_cases hin : offGridCentre n x ∈ openCubeSet (originCube d (m - 1))
    · have hbase := hclB hin
      have hKh0 : (0 : ℝ) ≤ Kh := holderHalfConst_nonneg_c1 hKh
      have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
        Real.rpow_nonneg (by norm_num) _
      have hHleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKh0
      have hcoef : (0 : ℝ) ≤
          max CestB CestA * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
        mul_nonneg hCest (Real.rpow_nonneg (by norm_num) _)
      have hstep := mul_le_mul_of_nonneg_left
        (by linarith only [hHleg] :
          Real.sqrt M.nu *
                Support.normalizedL2On (openCubeSet (originCube d m))
                  (fun y => Real.sqrt (vecNormSq (u.grad y)))
              + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg ≤
            Real.sqrt M.nu *
                Support.normalizedL2On (openCubeSet (originCube d m))
                  (fun y => Real.sqrt (vecNormSq (u.grad y)))
              + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
              + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) hcoef
      exact le_trans hbase hstep
    · exact hdispA n hn hpayn L hL u h g Kg Kh hdir hKg hKh hsup hgradh x hx hin
  have hpair := rootEnergyDensityPair_of_realDisplays M.nu
    (fun y => Real.sqrt (vecNormSq (u.grad y))) hx hn hCest
    (memLp_two_sqrt_vecNormSq_grad u) hclA hclB
  have hCle : ((3 : ℝ) ^ d * max CestB CestA) *
      Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) ≤
      max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) *
        Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hCestle
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcoef : ENNReal.ofReal
        (((3 : ℝ) ^ d * max CestB CestA) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) ≤
      ENNReal.ofReal
        (max (max C0 ((3 : ℝ) ^ d * max CestB CestA)) (max Crg CrgA) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) :=
    ENNReal.ofReal_le_ofReal hCle
  refine ⟨le_trans hpair.1 (mul_le_mul' hcoef (le_refl _)), fun hxin => ?_⟩
  exact le_trans (hpair.2 hxin) (mul_le_mul' hcoef (le_refl _))

end

end Algsuperdiff.Section4.Provider.Regularity
