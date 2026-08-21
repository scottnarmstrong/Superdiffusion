/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.SigmaBarBudget
import Algsuperdiff.Section4.Provider.GoodEvents.InductionState

/-!
# The `σ̄` index conversion at a two-scale gap, binder-free

This module closes that conversion **inside the anchor's own regime**: the
induction-state binder that `Annular.SigmaBarBudget.sigmaBar_ratio_le_four`
carries is discharged internally by
`GoodEvents.exists_allScalesInductionState`, at the landmark `m₀ := n+2` (resp.
`m₀ := n`), so nothing beyond `γ ≤ C^{-1} c⋆^{10}` is asked of the caller.
This is the `B1` wrapper pattern of `Provider/BoundsEaL/StepFourSigmaBar.lean`,
re-derived here so that the `BoundsEaL` tree is not imported.

```text
   σ̄_{n+2}^{-1} ≤ 4 σ̄_n^{-1}        (the direction the anchor's display needs)
   σ̄_n^{-1}     ≤ 7 σ̄_{n+2}^{-1}    (the converse, at the same regime)
```

Both constants are absolute numerals: no `s`, no `γ`, no `c⋆`, no dimension.
The regime is written in the frozen theorem's own shape `γ ≤ C^{-1} c⋆^{10}`
(the induction-state producer's shape `γ ≤ (C₀^{-1})^{10} c⋆^{10}` is reached
by exporting `C := C₀^{10}`).

## Where the constants come from

`σ̄` is *almost monotone* in the scale, in both directions, because the
induction state pins `σ̄_m^2` inside a factor-`4` window around `max(c⋆ γ^{-1}
3^{2γm}, ν^2)`, and that window's own ratio across two scales is `3^{4γ} ≤ 3`
at the standing `γ ≤ 1/4`.  Upward: the window is monotone in `m`, so the two
factor-`4` branches give `σ̄_n ≤ 4 σ̄_{n+2}`.  Downward: the extra `3^{4γ} ≤ 3`
gives `σ̄_{n+2}^2 ≤ 48 σ̄_n^2`, i.e. `σ̄_{n+2} ≤ 7 σ̄_n`.

## References

* ABK26, `e.shom.h.bounds`; `p.induction.bounds` proof.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. Two arithmetic helpers -/

/-- See the duplication disclosure. -/
private theorem three_rpow_mono {x y : ℝ} (h : x ≤ y) :
    (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- The two-scale window ratio at the standing `γ ≤ 1/4`. -/
private theorem three_rpow_four_gamma_le_three {gam : ℝ} (hgam : gam ≤ 1 / 4) :
    (3 : ℝ) ^ (4 * gam) ≤ 3 := by
  have h : (3 : ℝ) ^ (4 * gam) ≤ (3 : ℝ) ^ (1 : ℝ) :=
    three_rpow_mono (by linarith only [hgam])
  rwa [Real.rpow_one] at h

/-- The regime bridge: the anchor prints `γ ≤ C^{-1} c⋆^{10}`, the induction
state producer asks for `γ ≤ (C₀^{-1})^{10} c⋆^{10}`. -/
private theorem regime_bridge {C0 gam c : ℝ} (h : gam ≤ (C0 ^ (10 : ℕ))⁻¹ * c) :
    gam ≤ (C0⁻¹) ^ (10 : ℕ) * c := by
  rwa [inv_pow]

/-! ## 2. The two ratio readings of the state -/

/-- **`σ̄` is almost increasing.**  From the induction state at the landmark
`n+2`: `σ̄_n ≤ 4 σ̄_{n+2}`, in the inverse form the force leg consumes. -/
theorem inv_sigmaBar_add_two_le_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n + 2 ≤ m0) :
    ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ ≤ 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  have hidx : (n + 2 : ℤ) - 2 = n := by ring
  have hbase := Annular.sigmaBar_ratio_le_four M hS (m := n + 2) (n := n + 2)
    (by linarith only []) hn
  rw [hidx] at hbase
  have hB : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hstep := mul_le_mul_of_nonneg_right hbase (inv_nonneg.2 hB.le)
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hB), mul_one] at hstep
  exact hstep

/-- **The converse reading.**  From the induction state at the landmark `n+2`:
`σ̄_{n+2} ≤ 7 σ̄_n`, in inverse form.  The extra factor over the increasing
direction is the window's own two-scale ratio `3^{4γ} ≤ 3`. -/
theorem inv_sigmaBar_le_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n + 2 ≤ m0) :
    ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤ 7 * ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ := by
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hg14 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hA : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) := (Annealed.sigmaBar M (n + 2)).2
  have hB : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hlow := (hS.1 n (by linarith only [hn])).1
  have hup := (hS.1 (n + 2) hn).2
  have hcs0 : (0 : ℝ) ≤ Disorder.cstar M * M.gamma⁻¹ :=
    mul_nonneg (Disorder.cstar_characterization M).1.le (inv_nonneg.2 hg0.le)
  have hnu : (0 : ℝ) ≤ M.nu ^ 2 := sq_nonneg _
  have h4g : (0 : ℝ) < (3 : ℝ) ^ (4 * M.gamma) := Real.rpow_pos_of_pos (by norm_num) _
  have hshift : (3 : ℝ) ^ (2 * M.gamma * (((n + 2 : ℤ)) : ℝ)) =
      (3 : ℝ) ^ (4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (4 * M.gamma) := by
    have h := three_rpow_mono (x := (0 : ℝ)) (y := 4 * M.gamma)
      (by linarith only [hg0])
    rwa [Real.rpow_zero] at h
  have hmax : max (Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (((n + 2 : ℤ)) : ℝ))) (M.nu ^ 2)
      ≤ (3 : ℝ) ^ (4 * M.gamma) *
        max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
          (M.nu ^ 2) := by
    refine max_le ?_ ?_
    · rw [hshift]
      have hle : Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)) ≤
          max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
            (M.nu ^ 2) := le_max_left _ _
      have := mul_le_mul_of_nonneg_left hle h4g.le
      linarith only [this]
    · have hle : M.nu ^ 2 ≤
          max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
            (M.nu ^ 2) := le_max_right _ _
      have h1 := mul_le_mul_of_nonneg_left hle h4g.le
      have h2 := mul_le_mul_of_nonneg_right hone hnu
      linarith only [h1, h2]
  have hmaxnn : (0 : ℝ) ≤
      max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
        (M.nu ^ 2) := le_trans hnu (le_max_right _ _)
  have hthree := three_rpow_four_gamma_le_three hg14
  have hmax3 : (3 : ℝ) ^ (4 * M.gamma) *
      max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
        (M.nu ^ 2) ≤
      3 * max (Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (2 * M.gamma * (n : ℝ)))
        (M.nu ^ 2) := mul_le_mul_of_nonneg_right hthree hmaxnn
  have hsq : (Annealed.sigmaBar M (n + 2) : ℝ) ^ 2 ≤
      (7 * (Annealed.sigmaBar M n : ℝ)) ^ 2 := by
    have hexpand : (7 * (Annealed.sigmaBar M n : ℝ)) ^ 2 =
        49 * (Annealed.sigmaBar M n : ℝ) ^ 2 := by ring
    have hBsq : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) ^ 2 := by positivity
    rw [hexpand]
    linarith only [hup, hlow, hmax, hmax3, hBsq]
  have hle : (Annealed.sigmaBar M (n + 2) : ℝ) ≤ 7 * (Annealed.sigmaBar M n : ℝ) :=
    le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by linarith only [hB]) hsq
  have hratio : ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      (Annealed.sigmaBar M (n + 2) : ℝ) ≤ 7 := by
    have hinvn : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ := (inv_pos.2 hB).le
    calc ((Annealed.sigmaBar M n : ℝ))⁻¹ * (Annealed.sigmaBar M (n + 2) : ℝ)
        ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ * (7 * (Annealed.sigmaBar M n : ℝ)) :=
          mul_le_mul_of_nonneg_left hle hinvn
      _ = 7 := by field_simp
  have hstep := mul_le_mul_of_nonneg_right hratio (inv_nonneg.2 hA.le)
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hA), mul_one] at hstep
  exact hstep

/-! ## 3. The binder-free exports -/

/-- **The `σ̄` index conversion the anchor's force leg needs, binder-free.**

In the frozen theorem's own regime alone, `σ̄_{n+2}^{-1} ≤ 4 σ̄_n^{-1}` at
every integer scale: the induction-state binder is discharged internally. -/
theorem exists_inv_sigmaBar_add_two_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ n : ℤ, ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ ≤
          4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  obtain ⟨C0, hC0, hC⟩ := GoodEvents.exists_allScalesInductionState d
  refine ⟨C0 ^ (10 : ℕ), by positivity, ?_⟩
  intro M hreg n
  obtain ⟨E, -, hall⟩ := hC M (regime_bridge hreg)
  exact inv_sigmaBar_add_two_le_of_inductionState M (E := E) (hall (n + 2)) le_rfl

/-- **The converse conversion, binder-free**: `σ̄_n^{-1} ≤ 7 σ̄_{n+2}^{-1}`. -/
theorem exists_inv_sigmaBar_le_add_two (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ n : ℤ, ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
          7 * ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ := by
  obtain ⟨C0, hC0, hC⟩ := GoodEvents.exists_allScalesInductionState d
  refine ⟨C0 ^ (10 : ℕ), by positivity, ?_⟩
  intro M hreg n
  obtain ⟨E, -, hall⟩ := hC M (regime_bridge hreg)
  exact inv_sigmaBar_le_of_inductionState M (E := E) (hall (n + 2)) le_rfl

end

end Algsuperdiff.Section4.Provider.ExcessDecay
