/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootInterfaceMerge

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The boundary half of clause (A) -/

/-- **Clause (A) of the a.e. lattice display at the boundary centres.**

`RootInterfaceMerge.RootDisplayClauseAAe`'s body, character for character,
under the negated printed gate `offGridCentre n x ∉ □_{m-1}`. -/
def RootDisplayClauseABoundaryAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
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

/-! ## 2. Two distinct points of `□_m`, and the `∇h` leg's sign -/

/-- Two distinct points of `□_m`. -/
private theorem exists_ne_pair_originCube' [NeZero d] (m : ℤ) :
    ∃ x y : Vec d, x ∈ openCubeSet (originCube d m) ∧
      y ∈ openCubeSet (originCube d m) ∧ x ≠ y := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine ⟨(0 : Vec d), (fun _ => (1 / 4 : ℝ) * (3 : ℝ) ^ m), ?_, ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < (0 : ℝ) ∧ (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m
    exact ⟨by linarith only [h3], by linarith only [h3]⟩
  · rw [mem_openCubeSet_originCube_iff]
    exact fun _ => ⟨by linarith only [h3], by linarith only [h3]⟩
  · intro hEq
    have hi := congrFun hEq (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)
    simp only [Pi.zero_apply] at hi
    linarith only [hi, h3]

/-- The display's `∇h` leg is nonnegative at the printed Hölder constant. -/
private theorem rootDisplayHLeg_nonneg [NeZero d] {M : ABKModel d} {m : ℤ}
    {hdat : H1Function (openCubeSet (originCube d m))} {Kh : ℝ}
    (hKh : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Kh hdat.grad) :
    (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ) *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_originCube' (d := d) m
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKh0

/-! ## 3. The reduction -/

/-- **Clause (A) from clause (B) and the boundary half.**

On `offGridCentre n x ∈ □_{m-1}` clause (B)'s bound already gives clause (A)'s:
the extra `∇h` leg is nonnegative and the coefficient `C_est·3^{(1-α)(m-n)}` is
nonnegative, so the right-hand side only grows.  Off the gate the boundary
clause is used verbatim. -/
theorem RootDisplayClauseAAe_of_clauseB_boundary [NeZero d] {M : ABKModel d}
    {C1 Cest alpha : ℝ} (hCest : 0 ≤ Cest)
    (hB : RootDisplayClauseBAe M C1 Cest alpha)
    (hbd : RootDisplayClauseABoundaryAe M C1 Cest alpha) :
    RootDisplayClauseAAe M C1 Cest alpha := by
  intro m
  filter_upwards [hB m, hbd m] with omega hB' hbd'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx
  by_cases hin : offGridCentre n x ∈ openCubeSet (originCube d (m - 1))
  · have hbase := hB' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hin
    have hHleg := rootDisplayHLeg_nonneg (M := M) (hdat := hdat) hKh
    have hcoef : (0 : ℝ) ≤
        Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
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
  · exact hbd' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hin

/-- **The a.e. lattice display from clause (B) and the boundary half.**

`RootInterfaceMerge.RootLatticeDisplayAe_of_clauses` after the reduction: the
display needs only clause (B) and the boundary-centre estimate, at the same
`C₁`, the same `C_est` and the same `α`. -/
theorem RootLatticeDisplayAe_of_clauseB_boundary [NeZero d] {M : ABKModel d}
    {C1 Cest alpha : ℝ} (hCest : 0 ≤ Cest)
    (hB : RootDisplayClauseBAe M C1 Cest alpha)
    (hbd : RootDisplayClauseABoundaryAe M C1 Cest alpha) :
    RootLatticeDisplayAe M C1 Cest alpha :=
  RootLatticeDisplayAe_of_clauses
    (RootDisplayClauseAAe_of_clauseB_boundary hCest hB hbd) hB

/-- **`C_est` monotonicity of the boundary half.**  The alignment device
`RootInterfaceMerge.RootDisplayClauseAAe.mono_const` in the boundary shape, so
a boundary producer at its own `C_est` merges with clause (B) at the maximum. -/
theorem RootDisplayClauseABoundaryAe.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseABoundaryAe M C1 Cest alpha) :
    RootDisplayClauseABoundaryAe M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hout
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hout
  have hB0 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
      + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_originCube' (d := d) m
    have hKg0 : (0 : ℝ) ≤ Kg := hKg.nonneg hx0 hy0 hne
    have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hL2 : (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y))) :=
      mul_nonneg (Real.sqrt_nonneg _) (Support.normalizedL2On_nonneg _ _)
    have hGleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKg0
    have hHleg := rootDisplayHLeg_nonneg (M := M) (hdat := hdat) hKh
    linarith only [hL2, hGleg, hHleg]
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hrpow) hB0)

end

end Algsuperdiff.Section4.Provider.Regularity
