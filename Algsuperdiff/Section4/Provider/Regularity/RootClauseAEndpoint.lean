/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseABoundary
import Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalAssembly

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

/-- **The clause-(B) endpoint, restated in `RootDisplayClauseBAe`.**

`rootClauseB_display_offGrid_final` with its `∀ n L, n ≤ m → m ≤ L → payload →
…` prefix reordered into the slot's `∀ n, n ≤ m → payload → ∀ L, m ≤ L → …`.  A
pure binder move: no rewrite, no constant, no new hypothesis. -/
theorem clauseB_endpoint_as_clauseBAe (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg) :
    ∃ (Cedos Cannp Citer Cest gamma0 : ℝ) (k : ℕ),
      1 ≤ Cedos ∧ 0 < Cannp ∧ 0 ≤ Cest ∧ 0 < gamma0 ∧ 11 ≤ k ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
          RootDisplayClauseBAe M (stepOneC1 d Cedos Cannp Citer k) Cest alpha := by
  obtain ⟨Cedos, Cannp, Citer, Cest, gamma0, k, h1, h2, h3, h4, h5, hmain⟩ :=
    rootClauseB_display_offGrid_final d hd cstar Crg hcstar hCrg
  refine ⟨Cedos, Cannp, Citer, Cest, gamma0, k, h1, h2, h3, h4, h5, ?_⟩
  intro M hcs hg alpha ha0 ha m
  filter_upwards [hmain M hcs hg alpha ha0 ha m] with omega hom
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx
  exact hom n L hn hL hpay u hdat g Kg Kh hdir hKg hKh x hx

/-! ## 2. The root provider at a gated display hypothesis -/

/-- **The root provider with the display hypothesis gated.**

`RootInterfaceAe.anomalous_regularity_provider_of_latticeDisplayAe` asks for
the a.e. lattice display `(M, α)`.  Every §4.4 producer of it delivers it only
on its own regime `c⋆(M) = c⋆`, `γ(M) ≤ γ₀ᴰ`, `0 < α ≤ 1 - C_rgᴰ √γ`.  This is
the same provider on that regime: the exported threshold is `min γ₀ γ₀ᴰ` and
the exported `α`-range constant is `max (max C₀ (3^d C_est)) C_rgᴰ`, both
weakenings. -/
theorem anomalous_regularity_provider_of_latticeDisplayAe_gated (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) (Cedos Citer Cann Cest : ℝ) (k : ℕ) (hk : 11 ≤ k)
    (hCest : 0 ≤ Cest) (gammaD CrgD : ℝ) (hgammaD : 0 < gammaD) (hCrgD : 0 < CrgD)
    (hdisplay : ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gammaD →
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - CrgD * Real.sqrt M.gamma →
        RootLatticeDisplayAe M (stepOneC1 d Cedos Cann Citer k) Cest alpha) :
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
  obtain ⟨gamma0, C0, hg0pos, hC0pos, _, _, _, hpkg⟩ :=
    rootAssembly_aePackage d cstar hcstar Cedos Citer Cann k hk
  refine ⟨min gamma0 gammaD, max (max C0 ((3 : ℝ) ^ d * Cest)) CrgD,
    lt_min hg0pos hgammaD, lt_of_lt_of_le hCrgD (le_max_right _ _), ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hC0le : C0 ≤ max (max C0 ((3 : ℝ) ^ d * Cest)) CrgD :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hCestle : (3 : ℝ) ^ d * Cest ≤ max (max C0 ((3 : ℝ) ^ d * Cest)) CrgD :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have halphaC0 : alpha ≤ 1 - C0 * Real.sqrt M.gamma :=
    alphaRange_of_mono_const hC0le halpha
  have halphaD : alpha ≤ 1 - CrgD * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_max_right _ _) halpha
  obtain ⟨Z, hXmeas, hXtail, hae⟩ :=
    hpkg M hcs (rootGamma0_le_left hgamma) alpha halpha0 halphaC0 m
  refine ⟨minimalScaleX Z k, hXmeas, ?_, ?_⟩
  · intro N
    exact le_trans (hXtail N)
      (minimalScaleTail_ofReal_mono_const hC0pos hC0le hgpos)
  filter_upwards [hae,
    hdisplay M hcs (rootGamma0_le_right hgamma) alpha halpha0 halphaD m]
    with omega hpay hdisp
  intro L hL u h g Kg Kh hdir hKg hKh _hsup x hx n hn hgate
  have hzform := hdisp n hn (hpay n hn hgate) L hL u h g Kg Kh hdir hKg hKh x hx
  have hpair := rootEnergyDensityPair_of_realDisplays M.nu
    (fun y => Real.sqrt (vecNormSq (u.grad y))) hx hn hCest
    (memLp_two_sqrt_vecNormSq_grad u) hzform.1 hzform.2
  have hCle : ((3 : ℝ) ^ d * Cest) *
      Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) ≤
      max (max C0 ((3 : ℝ) ^ d * Cest)) CrgD *
        Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    mul_le_mul_of_nonneg_right hCestle
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcoef : ENNReal.ofReal
        (((3 : ℝ) ^ d * Cest) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) ≤
      ENNReal.ofReal
        (max (max C0 ((3 : ℝ) ^ d * Cest)) CrgD *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) :=
    ENNReal.ofReal_le_ofReal hCle
  refine ⟨le_trans hpair.1 (mul_le_mul' hcoef (le_refl _)), fun hxin => ?_⟩
  exact le_trans (hpair.2 hxin) (mul_le_mul' hcoef (le_refl _))

/-! ## 3. The endpoint: the root at ONE named boundary conditional -/

/-- **`t.regularity` from clause (B) and the boundary clause (A).**

The frozen root's entire conclusion — the `∃ γ₀ C` block, the `(M,α,m)`
binders, the minimal scale with its measurability and tail, and the a.e.
two-clause energy-density estimate with the sup binder in place — produced
from the unconditional clause-(B) endpoint and one named conditional: the
boundary-centre clause (A), asked at whatever `C₁` the clause-(B) chain pins
and at the producer's own `(C_est, γ₀, C_rg)`.

`hbdry` is a carried mathematical obligation, NOT a source premise: it is the
printed estimate itself at the centres `offGridCentre n x ∉ □_{m-1}`. -/
theorem anomalous_regularity_provider_of_boundaryClauseA (d : ℕ) [NeZero d]
    (hd : d ≠ 0) (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg)
    (hbdry : ∀ (Cedos Cannp Citer : ℝ) (k : ℕ), 1 ≤ Cedos → 0 < Cannp → 11 ≤ k →
      ∃ CestA gamma0A CrgA : ℝ, 0 ≤ CestA ∧ 0 < gamma0A ∧ 0 < CrgA ∧
        ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0A →
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - CrgA * Real.sqrt M.gamma →
            RootDisplayClauseABoundaryAe M
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
  have hCest : (0 : ℝ) ≤ max CestB CestA := le_trans hCestB (le_max_left _ _)
  refine anomalous_regularity_provider_of_latticeDisplayAe_gated d cstar hcstar Cedos
    Citer Cannp (max CestB CestA) k hk11 hCest (min gamma0B gamma0A) (max Crg CrgA)
    (lt_min hgamma0B hgamma0A) (lt_of_lt_of_le hCrg (le_max_left _ _)) ?_
  intro M hcs hgamma alpha halpha0 halpha
  exact RootLatticeDisplayAe_of_clauseB_boundary hCest
    ((hB M hcs (rootGamma0_le_left hgamma) alpha halpha0
      (alphaRange_of_mono_const (le_max_left _ _) halpha)).mono_const
      (le_max_left _ _))
    ((hA M hcs (rootGamma0_le_right hgamma) alpha halpha0
      (alphaRange_of_mono_const (le_max_right _ _) halpha)).mono_const
      (le_max_right _ _))

end

end Algsuperdiff.Section4.Provider.Regularity
