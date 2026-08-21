/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootInterfaceAe

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1.: the `γ₀` min-merge and the threshold merge -/

/-- **, the merge itself.**  Two `γ`-threshold clauses merge at the minimum of
their thresholds, which is still positive. -/
theorem rootGamma0_merge {P Q : ABKModel d → Prop} {g0 g1 : ℝ} (h0 : 0 < g0)
    (h1 : 0 < g1) (hP : ∀ M : ABKModel d, M.gamma ≤ g0 → P M)
    (hQ : ∀ M : ABKModel d, M.gamma ≤ g1 → Q M) :
    ∃ g : ℝ, 0 < g ∧ ∀ M : ABKModel d, M.gamma ≤ g → P M ∧ Q M :=
  ⟨min g0 g1, lt_min h0 h1, fun M hM =>
    ⟨hP M (le_trans hM (min_le_left _ _)), hQ M (le_trans hM (min_le_right _ _))⟩⟩

/-- The left projection of a merged threshold. -/
theorem rootGamma0_le_left {g0 g1 gamma : ℝ} (h : gamma ≤ min g0 g1) : gamma ≤ g0 :=
  le_trans h (min_le_left _ _)

/-- The right projection of a merged threshold. -/
theorem rootGamma0_le_right {g0 g1 gamma : ℝ} (h : gamma ≤ min g0 g1) : gamma ≤ g1 :=
  le_trans h (min_le_right _ _)

/-- Two producers, each with its own `γ₀` and its own `α`-range constant, merge at
`(min γ₀ γ₀', max')`: the threshold shrinks and the range constant grows, and
both moves are the weakening direction (`min_le_*` and
`RootAssemblyParameters.alphaRange_of_mono_const`).  This is the exact shape
the clause-(A)/clause-(B) assembly consumes. -/
theorem rootThreshold_merge {cstar : ℝ} {P Q : ABKModel d → ℝ → Prop}
    {g0 g1 C0 C1 : ℝ} (hg0 : 0 < g0) (hg1 : 0 < g1) (hC0 : 0 < C0)
    (hP : ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ g0 →
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C0 * Real.sqrt M.gamma → P M alpha)
    (hQ : ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ g1 →
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C1 * Real.sqrt M.gamma → Q M alpha) :
    ∃ g C : ℝ, 0 < g ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ g →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          P M alpha ∧ Q M alpha := by
  refine ⟨min g0 g1, max C0 C1, lt_min hg0 hg1, lt_of_lt_of_le hC0 (le_max_left _ _), ?_⟩
  intro M hcs hgamma alpha halpha0 halpha
  exact ⟨hP M hcs (rootGamma0_le_left hgamma) alpha halpha0
      (alphaRange_of_mono_const (le_max_left _ _) halpha),
    hQ M hcs (rootGamma0_le_right hgamma) alpha halpha0
      (alphaRange_of_mono_const (le_max_right _ _) halpha)⟩

/-! ## 2.: the `α`-range conversions -/

theorem alphaRange_of_maxLeft {gamma alpha C0 C1 : ℝ}
    (h : alpha ≤ 1 - max C0 C1 * Real.sqrt gamma) :
    alpha ≤ 1 - C0 * Real.sqrt gamma :=
  alphaRange_of_mono_const (le_max_left _ _) h

theorem alphaRange_of_maxRight {gamma alpha C0 C1 : ℝ}
    (h : alpha ≤ 1 - max C0 C1 * Real.sqrt gamma) :
    alpha ≤ 1 - C1 * Real.sqrt gamma :=
  alphaRange_of_mono_const (le_max_right _ _) h

/-- ** at the assembly's own constant `C = max C₀ (3^d C_est)`**: the producer's
`C_rg := C₀` range hypothesis follows from the root's printed range at the
enlarged constant.  This is the line `alphaRange_of_mono_const (le_max_left _
_) halpha` of the conditional root provider, named. -/
theorem alphaRange_at_assemblyConst {gamma alpha C0 Cest : ℝ} (d : ℕ)
    (h : alpha ≤ 1 - max C0 ((3 : ℝ) ^ d * Cest) * Real.sqrt gamma) :
    alpha ≤ 1 - C0 * Real.sqrt gamma :=
  alphaRange_of_mono_const (le_max_left _ _) h

/-! ## 3.: the two clauses of the a.e. display -/

/-- **Clause (A) of the a.e. lattice display**: the printed three-leg estimate
printed lattice centre.  The binder prefix and the conjunct body are
`RootInterfaceAe.RootLatticeDisplayAe`'s, character for character. -/
def RootDisplayClauseAAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
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
                          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)

/-- **Clause (B) of the a.e. lattice display**: the boundary-leg-free estimate,
gated by `z ∈ □_{m-1}`.  discharged this clause. -/
def RootDisplayClauseBAe (M : ABKModel d) (C1 Cest alpha : ℝ) : Prop :=
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
                (offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
                  Real.sqrt M.nu *
                      Support.normalizedL2On
                        (truncatedWindow (offGridCentre n x) m (n + 1))
                        (fun y => Real.sqrt (vecNormSq (u.grad y)))
                    ≤ Cest * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
                      (Real.sqrt M.nu *
                          Support.normalizedL2On (openCubeSet (originCube d m))
                            (fun y => Real.sqrt (vecNormSq (u.grad y)))
                        + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                            Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg))

/-- **, the pinning merge.**  Two clauses at the SAME `C₁` — hence the same
`(C_edos, C_ann', C_iter, k)` through `stepOneC1` — and the SAME `C_est` and
`alpha` assemble into the a.e. lattice display, with the two null sets merged
into one. -/
theorem RootLatticeDisplayAe_of_clauses {M : ABKModel d} {C1 Cest alpha : ℝ}
    (hA : RootDisplayClauseAAe M C1 Cest alpha)
    (hB : RootDisplayClauseBAe M C1 Cest alpha) :
    RootLatticeDisplayAe M C1 Cest alpha := by
  intro m
  filter_upwards [hA m, hB m] with omega hA' hB'
  intro n hn hpay L hL u h g Kg Kh hdir hKg hKh x hx
  exact ⟨hA' n hn hpay L hL u h g Kg Kh hdir hKg hKh x hx,
    hB' n hn hpay L hL u h g Kg Kh hdir hKg hKh x hx⟩

/-- The clause-(A) projection of the a.e. display. -/
theorem RootLatticeDisplayAe.clauseA {M : ABKModel d} {C1 Cest alpha : ℝ}
    (h : RootLatticeDisplayAe M C1 Cest alpha) :
    RootDisplayClauseAAe M C1 Cest alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx
  exact (h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx).1

/-- The clause-(B) projection of the a.e. display. -/
theorem RootLatticeDisplayAe.clauseB {M : ABKModel d} {C1 Cest alpha : ℝ}
    (h : RootLatticeDisplayAe M C1 Cest alpha) :
    RootDisplayClauseBAe M C1 Cest alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx
  exact (h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx).2

/-! ## 4., the `C_est` alignment -/

/-- Two distinct points of `□_m`.  Needed only to turn the display's own printed
Hölder binders into the sign facts `0 ≤ K_g`, `0 ≤ K_h` ('s bonus), which is
what makes the display's right-hand bracket nonnegative. -/
private theorem exists_ne_pair_originCube [NeZero d] (m : ℤ) :
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

/-- The nonnegativity of the display's right-hand bracket at the printed Hölder
constants. -/
private theorem rootDisplayBracket_nonneg [NeZero d] {M : ABKModel d} {m : ℤ}
    {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    {Kg Kh : ℝ}
    (hKg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKh : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Kh hdat.grad) :
    (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg
      + Real.sqrt (Annealed.sigmaBar M m : ℝ) *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_originCube (d := d) m
  have hKg0 : (0 : ℝ) ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hKh0 : (0 : ℝ) ≤ Kh := hKh.nonneg hx0 hy0 hne
  have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hL2 : (0 : ℝ) ≤ Real.sqrt M.nu *
      Support.normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (u.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Support.normalizedL2On_nonneg _ _)
  have hGleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKg0
  have hHleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ) *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKh0
  linarith only [hL2, hGleg, hHleg]

/-- The nonnegativity of clause (B)'s shorter bracket. -/
private theorem rootDisplayBracketB_nonneg [NeZero d] {M : ABKModel d} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d} {Kg : ℝ}
    (hKg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Kg g) :
    (0 : ℝ) ≤ Real.sqrt M.nu *
        Support.normalizedL2On (openCubeSet (originCube d m))
          (fun y => Real.sqrt (vecNormSq (u.grad y)))
      + Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_originCube (d := d) m
  have hKg0 : (0 : ℝ) ≤ Kg := hKg.nonneg hx0 hy0 hne
  have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hL2 : (0 : ℝ) ≤ Real.sqrt M.nu *
      Support.normalizedL2On (openCubeSet (originCube d m))
        (fun y => Real.sqrt (vecNormSq (u.grad y))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Support.normalizedL2On_nonneg _ _)
  have hGleg : (0 : ℝ) ≤ Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h3) hKg0
  linarith only [hL2, hGleg]

/-- **, the `C_est` alignment on clause (A).**  Enlarging `C_est` weakens the
clause, so two clause producers at different `C_est` are aligned at the
maximum. -/
theorem RootDisplayClauseAAe.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseAAe M C1 Cest alpha) :
    RootDisplayClauseAAe M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx
  have hB := rootDisplayBracket_nonneg (M := M) (u := u) (hdat := hdat) (g := g)
    hKg hKh
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle hrpow) hB
  exact le_trans hbase hstep

theorem RootDisplayClauseBAe.mono_const [NeZero d] {M : ABKModel d}
    {C1 Cest Cest' alpha : ℝ} (hle : Cest ≤ Cest')
    (h : RootDisplayClauseBAe M C1 Cest alpha) :
    RootDisplayClauseBAe M C1 Cest' alpha := by
  intro m
  filter_upwards [h m] with omega h'
  intro n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hin
  have hbase := h' n hn hpay L hL u hdat g Kg Kh hdir hKg hKh x hx hin
  have hB := rootDisplayBracketB_nonneg (M := M) (u := u) (g := g) hKg
  have hrpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle hrpow) hB
  exact le_trans hbase hstep

/-- **, the full alignment.**  A clause-(A) producer at `C_est^A` and a clause-(B)
producer at `C_est^B`, both at the SAME `C₁`, assemble into the a.e. lattice
display at `max C_est^A C_est^B`. -/
theorem RootLatticeDisplayAe_of_clauses_max [NeZero d] {M : ABKModel d}
    {C1 CestA CestB alpha : ℝ} (hA : RootDisplayClauseAAe M C1 CestA alpha)
    (hB : RootDisplayClauseBAe M C1 CestB alpha) :
    RootLatticeDisplayAe M C1 (max CestA CestB) alpha :=
  RootLatticeDisplayAe_of_clauses (hA.mono_const (le_max_left _ _))
    (hB.mono_const (le_max_right _ _))

end

end Algsuperdiff.Section4.Provider.Regularity
