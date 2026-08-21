/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootClauseABoundaryRegionSplit
import Algsuperdiff.Section4.Provider.Regularity.RootClauseAEndpointC1Floor

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `C₁` hits every sufficiently large target exactly -/

/-- **The Step-1 constant is onto, above its two `C_edos`-free floors.**

For every `V` clearing `max(2, 2d+2)`, the `C_iter` slot `4C_iter(k+1)/log 3`
and the floor `δ₀(C_fl,1,k)⁻¹`, there is a `C_edos ≥ C_fl` with `stepOne d
C_edos 1 C_iter k = V`.  The witness is `C_edos = √V/(4·3^{k/4})`, at which the
third slot of the `max` equals `V` and dominates the other two.  This is what
lets two lanes with different pinned `(C_iter, k)` read one and the same
`RootWindowPayload`. -/
theorem exists_cedos_stepOneC1_eq (d : ℕ) (Citer : ℝ) (k : ℕ) {Cfl V : ℝ}
    (hCfl : 1 ≤ Cfl) (hbase : max 2 (2 * (d : ℝ) + 2) ≤ V)
    (hiter : 4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ V)
    (hdelta0 : stepOneC1Delta0 Cfl 1 k ≤ V) :
    ∃ Cedos : ℝ, Cfl ≤ Cedos ∧ stepOneC1 d Cedos 1 Citer k = V := by
  have hT : (0 : ℝ) < stepOneThreePow k := stepOneThreePow_pos k
  have hTne : stepOneThreePow k ≠ 0 := ne_of_gt hT
  have h4T : (0 : ℝ) < 4 * stepOneThreePow k := by linarith only [hT]
  have hV2 : (2 : ℝ) ≤ V := le_trans (le_max_left _ _) hbase
  have hV0 : (0 : ℝ) ≤ V := by linarith only [hV2]
  have hs : stepOneS = 1 / 4 := by rw [stepOneS]
  have hsq : Real.sqrt V ^ (2 : ℕ) = V := Real.sq_sqrt hV0
  have hCflpos : (0 : ℝ) < Cfl := lt_of_lt_of_le one_pos hCfl
  have hfl2 : (4 * Cfl * stepOneThreePow k) ^ (2 : ℕ) ≤ V := by
    have h := hdelta0
    rw [stepOneC1Delta0_eq hCflpos one_pos k, hs] at h
    have hid : (2 * Cfl * 1 * stepOneThreePow k) ^ (2 : ℕ) / (1 / 4 : ℝ) =
        (4 * Cfl * stepOneThreePow k) ^ (2 : ℕ) := by ring
    rwa [hid] at h
  have hfl0 : (0 : ℝ) ≤ 4 * Cfl * stepOneThreePow k :=
    mul_nonneg (by linarith only [hCflpos]) hT.le
  have hflsqrt : 4 * Cfl * stepOneThreePow k ≤ Real.sqrt V := by
    have h := Real.sqrt_le_sqrt hfl2
    rwa [Real.sqrt_sq hfl0] at h
  refine ⟨Real.sqrt V / (4 * stepOneThreePow k), ?_, ?_⟩
  · rw [le_div_iff₀ h4T]
    linarith only [hflsqrt]
  · have hCedospos : (0 : ℝ) < Real.sqrt V / (4 * stepOneThreePow k) :=
      div_pos (Real.sqrt_pos.mpr (by linarith only [hV2])) h4T
    have hval : stepOneC1Delta0 (Real.sqrt V / (4 * stepOneThreePow k)) 1 k = V := by
      rw [stepOneC1Delta0_eq hCedospos one_pos k, hs]
      have he : 2 * (Real.sqrt V / (4 * stepOneThreePow k)) * 1 * stepOneThreePow k =
          Real.sqrt V / 2 := by
        field_simp
        ring
      rw [he, div_pow, hsq]
      ring
    rw [stepOneC1, hval, max_eq_right hiter, max_eq_right hbase]

/-! ## 2. The endpoint at the shell alone -/

/-- 's re-cut endpoint with its ONE named conditional narrowed from ALL boundary
lattice centres to the flush shell alone: the centres with `offGridCentre n x ∉
□_{m-1}` AND `¬(offGridCentre n x + □_{m-2} ⊆ □_m)`.  Everything else — the
minimal scale, its measurability and tail, the `γ₀` min-merge, the `α`-range
max-merge, the off-grid transfer — is//'s verbatim.

`hshell` is a carried mathematical obligation, NOT a source premise. -/
theorem anomalous_regularity_provider_of_boundaryShell (d : ℕ) [NeZero d]
    (hd : d ≠ 0) (cstar Crg : ℝ) (hcstar : 0 < cstar) (hCrg : 0 < Crg)
    (hshell : ∀ (Citer : ℝ) (k : ℕ), 11 ≤ k →
      ∃ CflS : ℝ, 1 ≤ CflS ∧
        ∀ Cedos : ℝ, CflS ≤ Cedos →
          ∃ CestS gamma0S CrgS : ℝ, 0 ≤ CestS ∧ 0 < gamma0S ∧ 0 < CrgS ∧
            ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0S →
              ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - CrgS * Real.sqrt M.gamma →
                RootDisplayClauseABoundaryC1ShellAe M
                  (stepOneC1 d Cedos 1 Citer k) CestS alpha) :
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
  refine anomalous_regularity_provider_of_boundaryClauseAC1Floor d hd cstar Crg hcstar
    hCrg ?_
  intro Citer k hk11
  obtain ⟨Cflg, Citerg, kg, hCflg, hkg11, hgateprod⟩ :=
    exists_rootDisplayClauseABoundaryC1GateAe d hd cstar Crg hcstar hCrg
  obtain ⟨CflS, hCflS, hshellprod⟩ := hshell Citer k hk11
  refine ⟨max 1 (max CflS (max (4 * Citerg * ((kg : ℝ) + 1) / Real.log 3)
      (stepOneC1Delta0 Cflg 1 kg))), le_max_left _ _, ?_⟩
  intro Cedos hfloor
  have hCedos1 : (1 : ℝ) ≤ Cedos := le_trans (le_max_left _ _) hfloor
  have hbase : max 2 (2 * (d : ℝ) + 2) ≤ stepOneC1 d Cedos 1 Citer k := by
    rw [stepOneC1]
    exact le_max_left _ _
  have hiter : 4 * Citerg * ((kg : ℝ) + 1) / Real.log 3 ≤
      stepOneC1 d Cedos 1 Citer k :=
    le_stepOneC1_of_le_cedos d hCedos1
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) hfloor)) Citer k
  have hdelta0 : stepOneC1Delta0 Cflg 1 kg ≤ stepOneC1 d Cedos 1 Citer k :=
    le_stepOneC1_of_le_cedos d hCedos1
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) hfloor)) Citer k
  obtain ⟨CedosG, hCedosG, hEq⟩ :=
    exists_cedos_stepOneC1_eq d Citerg kg hCflg hbase hiter hdelta0
  obtain ⟨CestG, gamma0G, hCestG, hgamma0G, hgateBody⟩ := hgateprod CedosG hCedosG
  obtain ⟨CestS, gamma0S, CrgS, hCestS, hgamma0S, hCrgS, hshellBody⟩ :=
    hshellprod Cedos (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfloor)
  refine ⟨max CestG CestS, min gamma0G gamma0S, max Crg CrgS,
    le_trans hCestG (le_max_left _ _), lt_min hgamma0G hgamma0S,
    lt_of_lt_of_le hCrg (le_max_left _ _), ?_⟩
  intro M hcs hg alpha halpha0 halpha
  have haG : alpha ≤ 1 - Crg * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_max_left _ _) halpha
  have haS : alpha ≤ 1 - CrgS * Real.sqrt M.gamma :=
    alphaRange_of_mono_const (le_max_right _ _) halpha
  have hG := (hgateBody M hcs (le_trans hg (min_le_left _ _)) alpha halpha0
    haG).mono_const (le_max_left CestG CestS)
  have hS := (hshellBody M hcs (le_trans hg (min_le_right _ _)) alpha halpha0
    haS).mono_const (le_max_right CestG CestS)
  rw [hEq] at hG
  exact RootDisplayClauseABoundaryC1Ae_of_gate_shell hG hS

end

end Algsuperdiff.Section4.Provider.Regularity
