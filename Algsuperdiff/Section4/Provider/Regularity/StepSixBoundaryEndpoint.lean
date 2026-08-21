/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepBoundaryAbsorption
import Algsuperdiff.Section4.Provider.Regularity.StepFiveBoundaryDelta

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Provider.ExcessDecay MeasureTheory

noncomputable section

/-! ## 1. The composition, with the flat leg held out -/

/-- **Step 6 with a held-out flat leg.**  The prefactor is replaced by `R` on the
geometric part, while the flat part `Fl` is absorbed separately (`habs`),
because absorption consumes the exponential itself. -/
theorem holderBoundary_compose {C E R A oscLo oscHi dataG dataHs Fl : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hER : E ≤ R) (hoscHi : 0 ≤ oscHi) (hdataG : 0 ≤ dataG)
    (hdataHs : 0 ≤ dataHs) (habs : E * Fl ≤ A)
    (hiter : oscLo ≤ C * E * (oscHi + C * dataG) + C * E * (dataHs + Fl)) :
    oscLo ≤ (C + C * C) * R * (oscHi + dataG + dataHs) + C * A := by
  have hR : 0 ≤ R := le_trans hE hER
  have hCE : C * E ≤ C * R := mul_le_mul_of_nonneg_left hER hC
  have h1 : C * E * oscHi ≤ C * R * oscHi := mul_le_mul_of_nonneg_right hCE hoscHi
  have h2 : C * E * (C * dataG) ≤ C * R * (C * dataG) :=
    mul_le_mul_of_nonneg_right hCE (mul_nonneg hC hdataG)
  have h3 : C * E * dataHs ≤ C * R * dataHs := mul_le_mul_of_nonneg_right hCE hdataHs
  have h4 : C * E * Fl = C * (E * Fl) := by ring
  have h5 : C * (E * Fl) ≤ C * A := mul_le_mul_of_nonneg_left habs hC
  have p1 : 0 ≤ C * C * R * oscHi :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hC) hR) hoscHi
  have p2 : 0 ≤ C * R * dataG := mul_nonneg (mul_nonneg hC hR) hdataG
  have p3 : 0 ≤ C * C * R * dataHs :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hC) hR) hdataHs
  have hexp : C * E * (oscHi + C * dataG) + C * E * (dataHs + Fl)
      = C * E * oscHi + C * E * (C * dataG) + C * E * dataHs + C * E * Fl := by ring
  have htgt : (C + C * C) * R * (oscHi + dataG + dataHs)
      = C * R * oscHi + C * C * R * oscHi + C * R * dataG + C * R * (C * dataG)
        + C * R * dataHs + C * C * R * dataHs := by ring
  linarith only [hiter, h1, h2, h3, h4, h5, p1, p2, p3, hexp, htgt]

/-! ## 2. The print's boundary Step 6: the flat leg `ε`-funded, `α`-free -/

/-- **`e.oscillation.Holder.bound` on the boundary branch, as the print builds
it**.

The flat `∇h` leg enters `δ_j` with the coefficient `ε_j`, so its window sum is
`S_ε ≤ 2 δ (m-n) = 2 C₁^{-1}(1-α)(m-n)`; the absorption `t e^t ≤ e^{2t}` then
delivers it at the printed exponent with the ABSOLUTE constant `4/log 3`:

```text
   oscLo ≤ (C+C²) 3^{(1/2)(1-α)(m-n)} ( oscHi + dataG + K_h-leg · 1 )
             + C (4/log 3) 3^{(1/2)(1-α)(m-n)} ( ‖∇h‖_{L^∞} · 1 ) .
```

No `α`, `γ` or `δ` survives in either constant. -/
theorem stepSixBoundary_holderBound_epsFunded (d : ℕ) {Cedos Cann Citer C alpha : ℝ}
    {k : ℕ} {n m : ℤ} {oscLo oscHi dataG Khleg Hinf ind Se : ℝ} (hC : 0 ≤ C)
    (hCiter : 0 ≤ Citer) (halpha : alpha ≤ 1) (hnm : n ≤ m) (hoscHi : 0 ≤ oscHi)
    (hdataG : 0 ≤ dataG) (hKhleg : 0 ≤ Khleg) (hHinf : 0 ≤ Hinf) (hind : 0 ≤ ind)
    (hSe0 : 0 ≤ Se)
    (hSe : Se ≤ 2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
      ((m : ℝ) - (n : ℝ)))
    (hiter : oscLo ≤
        C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) * (oscHi + C * dataG) +
          C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) * ((Khleg + Se * Hinf) * ind)) :
    oscLo ≤
      (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (oscHi + dataG + Khleg * ind) +
        C * (4 / Real.log 3 *
          Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Hinf * ind)) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hC1 : 0 < stepOneC1 d Cedos Cann Citer k := stepOneC1_pos d Cedos Cann Citer k
  have hC12 : (2 : ℝ) ≤ stepOneC1 d Cedos Cann Citer k := two_le_stepOneC1 d Cedos Cann Citer k
  have ht : 0 ≤ stepSixExponent alpha n m := stepSixExponent_nonneg halpha hnm
  have hHind : 0 ≤ Hinf * ind := mul_nonneg hHinf hind
  have hSeq : 2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha * ((m : ℝ) - (n : ℝ)) =
      2 * ((stepOneC1 d Cedos Cann Citer k)⁻¹ * stepSixExponent alpha n m) := by
    simp only [stepOneDelta, stepSixExponent]
    ring
  have habs0 := stepSixFlat_epsFunded_absorb (k := k) hC1 hCiter ht hSe0 hHind
    (step6_le_stepOneC1 d Cedos Cann Citer k) (by rw [← hSeq]; exact hSe)
  have hconst : 8 / (stepOneC1 d Cedos Cann Citer k * Real.log 3) ≤ 4 / Real.log 3 := by
    rw [div_le_div_iff₀ (mul_pos hC1 hlog) hlog]
    have h := mul_le_mul_of_nonneg_right hC12 hlog.le
    linarith only [h]
  have hRnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Hinf * ind) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hHind
  have habs : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
        stepSixExponent alpha n m) * (Se * (Hinf * ind)) ≤
      4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Hinf * ind) := by
    have hmono := mul_le_mul_of_nonneg_right hconst hRnn
    calc Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
          (Se * (Hinf * ind))
        ≤ 8 / (stepOneC1 d Cedos Cann Citer k * Real.log 3) *
            Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Hinf * ind) := habs0
      _ ≤ 4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
            (Hinf * ind) := by linarith only [hmono]
  have hiter' : oscLo ≤
      C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
            stepSixExponent alpha n m) * (oscHi + C * dataG) +
        C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
            stepSixExponent alpha n m) * (Khleg * ind + Se * (Hinf * ind)) := by
    have hid : (Khleg + Se * Hinf) * ind = Khleg * ind + Se * (Hinf * ind) := by ring
    rwa [hid] at hiter
  exact holderBoundary_compose hC (Real.exp_pos _).le
    (exp_stepOneC1_le_rpow_three_half d hCiter halpha hnm) hoscHi hdataG
    (mul_nonneg hKhleg hind) habs hiter'

/-! ## 3. The frozen statement's boundary Step 6: the `ε`-free leg, and its price -/

/-- **`e.oscillation.Holder.bound` on the boundary branch, with the frozen
statement's `ε`-free average leg.**

`δ_j` now carries the third `∇h` leg `C ‖(∇h)_{(z+□_{j+2})∩□_m}‖`, whose window
sum is `W = (m-n+1)` times a uniform cap `K_flat` and carries no `(1-α)`.  The
absorption still applies, but the constant on that leg is

```text
   4 / ((1-α) log 3) + 1 ,
```

and `epsFree_flat_price_sharp` shows the `(1-α)^{-1}` cannot be removed. -/
theorem stepSixBoundary_holderBound_epsFree (d : ℕ) {Cedos Cann Citer C alpha : ℝ}
    {k : ℕ} {n m : ℤ} {oscLo oscHi dataG Khleg Hinf Kflat ind Se W : ℝ} (hC : 0 ≤ C)
    (hCiter : 0 ≤ Citer) (halpha : alpha < 1) (hnm : n ≤ m) (hoscHi : 0 ≤ oscHi)
    (hdataG : 0 ≤ dataG) (hKhleg : 0 ≤ Khleg) (hHinf : 0 ≤ Hinf) (hKflat : 0 ≤ Kflat)
    (hind : 0 ≤ ind) (hSe0 : 0 ≤ Se)
    (hSe : Se ≤ 2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
      ((m : ℝ) - (n : ℝ)))
    (hW : W = ((m : ℝ) - (n : ℝ)) + 1)
    (hiter : oscLo ≤
        C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) * (oscHi + C * dataG) +
          C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) *
            ((Khleg + Se * Hinf + W * Kflat) * ind)) :
    oscLo ≤
      (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (oscHi + dataG + Khleg * ind) +
        C * (4 / Real.log 3 *
              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Hinf * ind) +
            (4 / ((1 - alpha) * Real.log 3) + 1) *
              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Kflat * ind)) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have halpha' : alpha ≤ 1 := le_of_lt halpha
  have hC1 : 0 < stepOneC1 d Cedos Cann Citer k := stepOneC1_pos d Cedos Cann Citer k
  have hC12 : (2 : ℝ) ≤ stepOneC1 d Cedos Cann Citer k := two_le_stepOneC1 d Cedos Cann Citer k
  have ht : 0 ≤ stepSixExponent alpha n m := stepSixExponent_nonneg halpha' hnm
  have hRnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) :=
    Real.rpow_nonneg (by norm_num) _
  have hHind : 0 ≤ Hinf * ind := mul_nonneg hHinf hind
  have hKind : 0 ≤ Kflat * ind := mul_nonneg hKflat hind
  -- the `ε`-funded flat leg, `α`-free
  have hSeq : 2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha * ((m : ℝ) - (n : ℝ)) =
      2 * ((stepOneC1 d Cedos Cann Citer k)⁻¹ * stepSixExponent alpha n m) := by
    simp only [stepOneDelta, stepSixExponent]
    ring
  have habs0 := stepSixFlat_epsFunded_absorb (k := k) hC1 hCiter ht hSe0 hHind
    (step6_le_stepOneC1 d Cedos Cann Citer k) (by rw [← hSeq]; exact hSe)
  have hconst : 8 / (stepOneC1 d Cedos Cann Citer k * Real.log 3) ≤ 4 / Real.log 3 := by
    rw [div_le_div_iff₀ (mul_pos hC1 hlog) hlog]
    have h := mul_le_mul_of_nonneg_right hC12 hlog.le
    linarith only [h]
  have habsA : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
        stepSixExponent alpha n m) * (Se * (Hinf * ind)) ≤
      4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
        (Hinf * ind) := by
    have hmono := mul_le_mul_of_nonneg_right hconst (mul_nonneg hRnn hHind)
    linarith only [habs0, hmono]
  -- the `ε`-free flat leg: the `(1-α)^{-1}` price, plus the one extra scale
  have hprice := stepSixFlat_epsFree_price (H := Kflat * ind) (Cedos := Cedos) (Cann := Cann)
    (k := k) d hCiter halpha hnm hKind
  have hone : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
        stepSixExponent alpha n m) * (Kflat * ind) ≤
      Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Kflat * ind) :=
    mul_le_mul_of_nonneg_right (exp_stepOneC1_le_rpow_three_half d hCiter halpha' hnm) hKind
  have habsB : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
        stepSixExponent alpha n m) * (W * (Kflat * ind)) ≤
      (4 / ((1 - alpha) * Real.log 3) + 1) *
        Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Kflat * ind) := by
    have hsplit : W * (Kflat * ind) = ((m : ℝ) - (n : ℝ)) * (Kflat * ind) + (Kflat * ind) := by
      rw [hW]; ring
    rw [hsplit, mul_add]
    linarith only [hprice, hone]
  have habs : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
        stepSixExponent alpha n m) * (Se * (Hinf * ind) + W * (Kflat * ind)) ≤
      4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Hinf * ind) +
        (4 / ((1 - alpha) * Real.log 3) + 1) *
          Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Kflat * ind) := by
    have hid : Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
          stepSixExponent alpha n m) * (Se * (Hinf * ind) + W * (Kflat * ind))
        = Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) * (Se * (Hinf * ind)) +
          Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) * (W * (Kflat * ind)) := by ring
    rw [hid]
    linarith only [habsA, habsB]
  have hiter' : oscLo ≤
      C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
            stepSixExponent alpha n m) * (oscHi + C * dataG) +
        C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
            stepSixExponent alpha n m) *
          (Khleg * ind + (Se * (Hinf * ind) + W * (Kflat * ind))) := by
    have hid : (Khleg + Se * Hinf + W * Kflat) * ind
        = Khleg * ind + (Se * (Hinf * ind) + W * (Kflat * ind)) := by ring
    rwa [hid] at hiter
  exact holderBoundary_compose hC (Real.exp_pos _).le
    (exp_stepOneC1_le_rpow_three_half d hCiter halpha' hnm) hoscHi hdataG
    (mul_nonneg hKhleg hind) habs hiter'

/-! ## 4. The display's `∇h` leg from the root's `K_h` binder pair -/

/-- **The three boundary `∇h` legs collapse into `3^{m/2} K_h`.**

```text
   K_h-leg / (1-r₂) + ‖∇h‖_{L^∞} + K_flat
     ≤ ( C/(1-r₂) + 2 ) · 3^{m/2} K_h .
``` -/
theorem stepSixBoundary_hLegs_collapse {d : ℕ} {C : ℝ} (hC : 0 ≤ C) {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) {gradh : Vec d → Vec d} {Kh : ℝ} (hKh : 0 ≤ Kh)
    (hsem : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh gradh)
    (hint : ∀ i, IntegrableOn (fun y => gradh y i) (truncatedWindow z m (j + 2)) volume)
    (hpt : ∀ y ∈ openCubeSet (originCube d m), ‖gradh y‖ ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) :
    stepFiveKh C m gradh / (1 - stepFiveRatioH) + stepFiveLinftyNorm m gradh +
        stepFiveFlatAvgLeg 1 m z gradh j ≤
      (C / (1 - stepFiveRatioH) + 2) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  have hr : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have hKfull : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh
  have hsem' : stepFiveHalfSeminorm m gradh ≤ Kh :=
    stepFiveHalfSeminorm_le_of_holderSeminormBound hKh hsem
  have hKhleg : stepFiveKh C m gradh ≤ C * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
    rw [stepFiveKh]
    have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsem' h3) hC
  have hdiv : stepFiveKh C m gradh / (1 - stepFiveRatioH) ≤
      C / (1 - stepFiveRatioH) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
    rw [div_le_iff₀ hr]
    have hid : C / (1 - stepFiveRatioH) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) *
        (1 - stepFiveRatioH) = C * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
      field_simp
    linarith only [hKhleg, hid]
  have hinf : stepFiveLinftyNorm m gradh ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    stepFiveLinftyNorm_le_of_bound hKfull hpt
  have hflat : stepFiveFlatAvgLeg 1 m z gradh j ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
    have h := stepFiveFlatAvgLeg_le (C := 1) zero_le_one hz hKfull hint hpt
    linarith only [h]
  have hid2 : (C / (1 - stepFiveRatioH) + 2) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)
      = C / (1 - stepFiveRatioH) * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) +
        (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) + (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
    ring
  linarith only [hdiv, hinf, hflat, hid2]

end

end Algsuperdiff.Section4.Provider.Regularity
