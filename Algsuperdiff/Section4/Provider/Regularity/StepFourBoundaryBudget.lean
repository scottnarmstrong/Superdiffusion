/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseInterface
import Algsuperdiff.Section4.Provider.Regularity.StepFiveBoundaryDelta

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory

noncomputable section

/-! ## 1. The window count -/

/-- `|Icc n m| = (m-n)+1` as a real, for `n ≤ m`. -/
theorem card_Icc_cast (n m : ℤ) (hnm : n ≤ m) :
    (((Finset.Icc n m).card : ℕ) : ℝ) = ((m : ℝ) - (n : ℝ)) + 1 := by
  rw [Int.card_Icc]
  have h : (((m + 1 - n).toNat : ℤ) : ℝ) = ((m + 1 - n : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (Int.toNat_of_nonneg (by omega))
  push_cast at h ⊢
  linarith only [h]

/-! ## 2. The boundary budget kit: legs -/

/-- **`e.sum.delta.j.bound` with the anchor's `ε`-free flat leg carried.**

`δ_j = A^g_j + (A^h_j + ε_j H + F) 𝟙` with `A^g`, `A^h` geometrically dominated
from the top scale and `F` a constant (flat) leg.  Then

```text
   ∑_{j=n}^{m} δ_j ≤ K_g/(1-r₁) + ( K_h/(1-r₂) + S_ε H + W F ) 𝟙 ,   W = (m-n)+1 .
```

The flat leg's contribution is `W`-linear: it is the only summand whose
coefficient is not bought by the `ε`-budget. -/
theorem sum_Icc_top_boundaryDelta_le_of_legs
    {δ Ag Ah ε : ℤ → ℝ} {r₁ r₂ Kg Kh Hinf Flat Se W ind : ℝ} {n m : ℤ} (hnm : n ≤ m)
    (hr₁0 : 0 < r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 < r₂) (hr₂1 : r₂ < 1)
    (hAg0 : 0 ≤ Ag m) (hAgd : ∀ j : ℤ, j ≤ m → Ag j ≤ Kg * r₁ ^ (m - j))
    (hAh0 : 0 ≤ Ah m) (hAhd : ∀ j : ℤ, j ≤ m → Ah j ≤ Kh * r₂ ^ (m - j))
    (hSe : ∑ j ∈ Finset.Icc n m, ε j ≤ Se)
    (hHinf : 0 ≤ Hinf) (hind0 : 0 ≤ ind) (hW : W = ((m : ℝ) - (n : ℝ)) + 1)
    (hδ : ∀ j : ℤ, δ j = Ag j + (Ah j + ε j * Hinf + Flat) * ind) :
    ∑ j ∈ Finset.Icc n m, δ j ≤
      Kg / (1 - r₁) + (Kh / (1 - r₂) + Se * Hinf + W * Flat) * ind := by
  have hgleg : ∑ j ∈ Finset.Icc n m, Ag j ≤ Kg / (1 - r₁) :=
    sum_Icc_top_le_of_zpow_dominated hr₁0 hr₁1 hnm hAg0 hAgd
  have hhleg : ∑ j ∈ Finset.Icc n m, Ah j ≤ Kh / (1 - r₂) :=
    sum_Icc_top_le_of_zpow_dominated hr₂0 hr₂1 hnm hAh0 hAhd
  have hflat : ∑ _j ∈ Finset.Icc n m, Flat = W * Flat := by
    rw [Finset.sum_const, nsmul_eq_mul, card_Icc_cast n m hnm, hW]
  have heq : ∑ j ∈ Finset.Icc n m, δ j
      = (∑ j ∈ Finset.Icc n m, Ag j)
        + ((∑ j ∈ Finset.Icc n m, Ah j) + (∑ j ∈ Finset.Icc n m, ε j) * Hinf
            + (∑ _j ∈ Finset.Icc n m, Flat)) * ind := by
    rw [Finset.sum_congr rfl fun j _ => hδ j]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [heq, hflat]
  have hmid : (∑ j ∈ Finset.Icc n m, Ah j) + (∑ j ∈ Finset.Icc n m, ε j) * Hinf + W * Flat
      ≤ Kh / (1 - r₂) + Se * Hinf + W * Flat := by
    have h := mul_le_mul_of_nonneg_right hSe hHinf
    linarith only [hhleg, h]
  have hmul := mul_le_mul_of_nonneg_right hmid hind0
  linarith only [hgleg, hmul]

/-! ## 3. `stepFourDeltaOut` in the boundary four-leg shape -/

/-- The single constant the Step-4 boundary output collapses to: `C_rem V_d C
(s^{-4} s^{-3/2} + 8 s^{-7} + s^{-6})`. -/
def stepFourBoundaryDeltaConst (Crem Vd Cst s : ℝ) : ℝ :=
  Crem * Vd *
    (Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))))

theorem stepFourBoundaryDeltaConst_nonneg {Crem Vd Cst s : ℝ} (hCV : 0 ≤ Crem * Vd)
    (hCst : 0 ≤ Cst) (hs : 0 < s) : 0 ≤ stepFourBoundaryDeltaConst Crem Vd Cst s := by
  have h4 : (0 : ℝ) ≤ s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hs.le _)
  have h7 : (0 : ℝ) ≤ s ^ (-(7 : ℝ)) := Real.rpow_nonneg hs.le _
  have h6 : (0 : ℝ) ≤ s ^ (-(6 : ℝ)) := Real.rpow_nonneg hs.le _
  rw [stepFourBoundaryDeltaConst]
  exact mul_nonneg hCV (mul_nonneg hCst (by linarith only [h4, h7, h6]))

/-- **The Step-4 boundary output in the budget's own grouping.**

```text
   stepFourDeltaOut ≤ C_bd 3^{n/2} σ̄_n^{-1} K_g
                    + ( C_bd 3^{n/2} K_h + (C_bd ε_j) K_hinf + C_bd K_hinf ) ,
```

i.e. `A^g_n + (A^h_n + ε'_n H + F)` with `H = F/C_bd = K_hinf`.  The summand is
the `ε`-free one. -/
theorem stepFourDeltaOut_le_boundaryFourLegs {Crem Vd Cst s epsj Khinf SigInvN Kg Kh : ℝ}
    {n : ℤ} (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ Cst) (hs : 0 < s) (heps0 : 0 ≤ epsj)
    (hKhinf : 0 ≤ Khinf) (hSig0 : 0 ≤ SigInvN) (hKg0 : 0 ≤ Kg) (hKh0 : 0 ≤ Kh) :
    stepFourDeltaOut Crem Vd Cst s epsj Khinf SigInvN Kg Kh n ≤
      stepFourBoundaryDeltaConst Crem Vd Cst s *
          ((3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg) +
        (stepFourBoundaryDeltaConst Crem Vd Cst s * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          (stepFourBoundaryDeltaConst Crem Vd Cst s * epsj) * Khinf +
          stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hX : (0 : ℝ) ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ))) :=
    mul_nonneg hCst (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hs.le _))
  have hY : (0 : ℝ) ≤ Cst * s ^ (-(7 : ℝ)) := mul_nonneg hCst (Real.rpow_nonneg hs.le _)
  have hZ : (0 : ℝ) ≤ Cst * s ^ (-(6 : ℝ)) := mul_nonneg hCst (Real.rpow_nonneg hs.le _)
  -- the four coefficient comparisons, each against the single constant
  have hc1 : Cst * s ^ (-(4 : ℝ)) * (s ^ (-(3 / 2 : ℝ)) * (1 / 9))
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  have hc2 : 8 * (Cst * s ^ (-(7 : ℝ)))
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  have hc3 : Cst * s ^ (-(6 : ℝ))
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  have hc4 : Cst * s ^ (-(6 : ℝ)) * (1 / 9)
      ≤ Cst * (s ^ (-(4 : ℝ)) * s ^ (-(3 / 2 : ℝ)) + 8 * s ^ (-(7 : ℝ)) + s ^ (-(6 : ℝ))) := by
    linarith only [hX, hY, hZ]
  -- transport each comparison through `Crem V_d` and the nonnegative data factor
  have hf1 : 0 ≤ epsj * Khinf := mul_nonneg heps0 hKhinf
  have hf2 : 0 ≤ (3 : ℝ) ^ ((n : ℝ) / 2) * SigInvN * Kg :=
    mul_nonneg (mul_nonneg h3 hSig0) hKg0
  have hf3 : 0 ≤ (3 : ℝ) ^ ((n : ℝ) / 2) * Kh := mul_nonneg h3 hKh0
  have hm1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 hCV) hf1
  have hm2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 hCV) hf2
  have hm3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc3 hCV) hf3
  have hm4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc4 hCV) hKhinf
  rw [stepFourDeltaOut, stepFourBoundaryDeltaConst]
  linarith only [hm1, hm2, hm3, hm4]

/-! ## 4. The composed boundary budget for the Step-4 output -/

/-- **The Step-4 boundary output, summed over the iteration window.**

With the two decaying legs dominated geometrically and the `ε`-sum budget in
hand, the window sum of the Step-4 output is

```text
   ∑_{j=n}^{m} δ_j ≤ K_g/(1-r₁) + ( K_h/(1-r₂) + S_ε (C_bd K_hinf)
                                     + W · (C_bd K_hinf) ) ,     W = (m-n)+1 ,
```

which is `dataG + dataH_∂` in `StepFiveBoundaryDelta.stepFiveDataHBoundary`'s
shape at `ind = 1` (the boundary branch).  The last summand is the `ε`-free
one: `W`-linear, with no `(1-α)`. -/
theorem sum_Icc_top_stepFourDeltaOut_le {Crem Vd Cst s Khinf Kg Kh Se W : ℝ}
    {SigInvN eps δ Ag Ah : ℤ → ℝ} {r₁ r₂ : ℝ} {n m : ℤ} (hnm : n ≤ m)
    (hCV : 0 ≤ Crem * Vd) (hCst : 0 ≤ Cst) (hs : 0 < s) (hKhinf : 0 ≤ Khinf)
    (hr₁0 : 0 < r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 < r₂) (hr₂1 : r₂ < 1)
    (hAg0 : 0 ≤ Ag m) (hAgd : ∀ j : ℤ, j ≤ m → Ag j ≤ Kg * r₁ ^ (m - j))
    (hAh0 : 0 ≤ Ah m) (hAhd : ∀ j : ℤ, j ≤ m → Ah j ≤ Kh * r₂ ^ (m - j))
    (hSe : ∑ j ∈ Finset.Icc n m, eps j ≤ Se) (hW : W = ((m : ℝ) - (n : ℝ)) + 1)
    (hAgdef : ∀ j : ℤ, Ag j = stepFourBoundaryDeltaConst Crem Vd Cst s *
      ((3 : ℝ) ^ ((j : ℝ) / 2) * SigInvN j * Kg))
    (hAhdef : ∀ j : ℤ, Ah j = stepFourBoundaryDeltaConst Crem Vd Cst s *
      ((3 : ℝ) ^ ((j : ℝ) / 2) * Kh))
    (hδdef : ∀ j : ℤ, δ j = stepFourDeltaOut Crem Vd Cst s (eps j) Khinf (SigInvN j) Kg Kh j)
    (heps0 : ∀ j : ℤ, 0 ≤ eps j) (hSig0 : ∀ j : ℤ, 0 ≤ SigInvN j) (hKg0 : 0 ≤ Kg)
    (hKh0 : 0 ≤ Kh) :
    ∑ j ∈ Finset.Icc n m, δ j ≤
      Kg / (1 - r₁) +
        (Kh / (1 - r₂) + Se * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) +
          W * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)) := by
  have hCbd : 0 ≤ stepFourBoundaryDeltaConst Crem Vd Cst s :=
    stepFourBoundaryDeltaConst_nonneg hCV hCst hs
  have hHinf : 0 ≤ stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf := mul_nonneg hCbd hKhinf
  have hstep : ∀ j : ℤ, δ j ≤
      Ag j + (Ah j + eps j * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) +
        stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) := by
    intro j
    have h := stepFourDeltaOut_le_boundaryFourLegs (Crem := Crem) (Vd := Vd) (Cst := Cst)
      (s := s) (epsj := eps j) (Khinf := Khinf) (SigInvN := SigInvN j) (Kg := Kg) (Kh := Kh)
      (n := j) hCV hCst hs (heps0 j) hKhinf (hSig0 j) hKg0 hKh0
    rw [hδdef j, hAgdef j, hAhdef j]
    have hid : (stepFourBoundaryDeltaConst Crem Vd Cst s * eps j) * Khinf
        = eps j * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) := by ring
    linarith only [h, hid]
  have hsum : ∑ j ∈ Finset.Icc n m, δ j ≤
      ∑ j ∈ Finset.Icc n m,
        (Ag j + (Ah j + eps j * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) +
          stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)) :=
    Finset.sum_le_sum fun j _ => hstep j
  have hkit := sum_Icc_top_boundaryDelta_le_of_legs (Ag := Ag) (Ah := Ah) (ε := eps)
    (δ := fun j => Ag j + (Ah j + eps j *
      (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) +
      stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf))
    (Kg := Kg) (Kh := Kh) (Hinf := stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)
    (Flat := stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) (Se := Se) (W := W)
    (ind := 1) hnm hr₁0 hr₁1 hr₂0 hr₂1 hAg0 hAgd hAh0 hAhd hSe hHinf zero_le_one hW
    (fun j => by ring)
  have hone : Kg / (1 - r₁) +
      (Kh / (1 - r₂) + Se * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) +
        W * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)) * 1 =
      Kg / (1 - r₁) +
        (Kh / (1 - r₂) + Se * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf) +
          W * (stepFourBoundaryDeltaConst Crem Vd Cst s * Khinf)) := by ring
  linarith only [hsum, hkit, hone]

end

end Algsuperdiff.Section4.Provider.Regularity
