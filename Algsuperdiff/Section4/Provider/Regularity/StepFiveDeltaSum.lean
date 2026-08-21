/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFiveDeltaFamily

/-!
# `t.regularity` Step 5: `e.sum.delta.j.bound` at the concrete family

## The target

ABK26 `t.regularity` Step 5, (`e.sum.delta.j.bound`), at the `δ_j` of
`StepFiveDeltaFamily`:

```text
  ∑_{j=n}^{m-1} δ_j  ≤  C 3^{m/2} σ̄_m^{-1} [g]_{W̲^{1/2,∞}(□_m)}
      + C ( 3^{m/2} [∇h]_{W̲^{1/2,∞}(□_m)}
            + C₁^{-1}(1-α)(m-n) ‖∇h‖_{L^∞(□_m)} ) 1_{z ∉ □_{m-1}} .
```

```text
  r₁ := 3^{-(1/2-γ)} ,   r₂ := 3^{-1/2} ,
  K_g := C · 4 · 3^{m/2} σ̄_m^{-1} [g] ,   K_h := C · 3^{m/2} [∇h] ,
  Hinf := C ‖∇h‖_{L^∞(□_m)} ,   ind := 1_{z ∉ □_{m-1}} ,
```

## The two windows

`l.iteration.lemma` sums `δ` over `Finset.Icc n m`; the manuscript's display is
over `[n, m-1]` ('s deviation D1).  Both are proved:

* `sum_Icc_top_stepFiveDelta_le` — the AN's window `Icc n m`, at the
  coefficient `1/(1-r)` (one extra top term `δ_m ≤ K`), packaged as
  `stepFiveDataG + stepFiveDataH` for's `dataG`/`dataH` slots.

The two abstract-real kit lemmas for the anchor's window
(`sum_Icc_top_le_of_zpow_dominated`, `sum_Icc_top_delta_le_of_legs`) are stated
here rather than's tracked files, which are pinned to the printed window; they
are the same downward induction, re-used through's own
`sum_Icc_le_of_zpow_dominated` plus the single top term.

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal
open scoped Classical

noncomputable section

/-! ## 1. The kit lemmas on the anchor's window `Icc n m` -/

/-- **The geometric tail on the anchor's window.**  For a nonnegative family
dominated from the top scale, `f j ≤ K r^{m-j}` with `0 < r < 1`,

```text
   ∑_{j=n}^{m} f j  ≤  K / (1 - r)          uniformly in n ≤ m .
```

One extra term over's printed-window `sum_Icc_le_of_zpow_dominated`, namely `f
m ≤ K`, turns its `K r/(1-r)` into `K/(1-r)`. -/
theorem sum_Icc_top_le_of_zpow_dominated {r K : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {f : ℤ → ℝ} {n m : ℤ} (hn : n ≤ m) (hf0 : 0 ≤ f m)
    (hdom : ∀ j : ℤ, j ≤ m → f j ≤ K * r ^ (m - j)) :
    ∑ j ∈ Finset.Icc n m, f j ≤ K / (1 - r) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hsplit : Finset.Icc n m = insert m (Finset.Icc n (m - 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : m ∉ Finset.Icc n (m - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have htail := sum_Icc_le_of_zpow_dominated hr0 hr1 hn hf0 hdom
  have htail' : (∑ j ∈ Finset.Icc n (m - 1), f j) * (1 - r) ≤ K * r :=
    (le_div_iff₀ h1r).mp htail
  have hfm : f m ≤ K := by
    have hd := hdom m le_rfl
    have h0 : m - m = (0 : ℤ) := by omega
    rwa [h0, zpow_zero, mul_one] at hd
  have hfm' : f m * (1 - r) ≤ K * (1 - r) := mul_le_mul_of_nonneg_right hfm h1r.le
  rw [hsplit, Finset.sum_insert hnot, le_div_iff₀ h1r]
  linarith only [htail', hfm']

/-- **`e.sum.delta.j.bound` on the anchor's window**, with the three legs abstract
—'s `sum_Icc_delta_le_of_legs` read over `Finset.Icc n m`:

```text
   ∑_{j=n}^{m} δ_j ≤ K_g/(1-r₁) + ( K_h/(1-r₂) + S_ε H ) 𝟙 .
```

The boundary leg is carried. -/
theorem sum_Icc_top_delta_le_of_legs
    {δ Ag Ah ε : ℤ → ℝ} {r₁ r₂ Kg Kh Hinf Se ind : ℝ} {n m : ℤ} (hnm : n ≤ m)
    (hr₁0 : 0 < r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 < r₂) (hr₂1 : r₂ < 1)
    (hAg0 : 0 ≤ Ag m) (hAgd : ∀ j : ℤ, j ≤ m → Ag j ≤ Kg * r₁ ^ (m - j))
    (hAh0 : 0 ≤ Ah m) (hAhd : ∀ j : ℤ, j ≤ m → Ah j ≤ Kh * r₂ ^ (m - j))
    (hSe : ∑ j ∈ Finset.Icc n m, ε j ≤ Se)
    (hHinf : 0 ≤ Hinf) (hind0 : 0 ≤ ind)
    (hδ : ∀ j : ℤ, δ j = Ag j + (Ah j + ε j * Hinf) * ind) :
    ∑ j ∈ Finset.Icc n m, δ j ≤ Kg / (1 - r₁) + (Kh / (1 - r₂) + Se * Hinf) * ind := by
  have hgleg : ∑ j ∈ Finset.Icc n m, Ag j ≤ Kg / (1 - r₁) :=
    sum_Icc_top_le_of_zpow_dominated hr₁0 hr₁1 hnm hAg0 hAgd
  have hhleg : ∑ j ∈ Finset.Icc n m, Ah j ≤ Kh / (1 - r₂) :=
    sum_Icc_top_le_of_zpow_dominated hr₂0 hr₂1 hnm hAh0 hAhd
  have heq : ∑ j ∈ Finset.Icc n m, δ j
      = (∑ j ∈ Finset.Icc n m, Ag j)
        + ((∑ j ∈ Finset.Icc n m, Ah j)
            + (∑ j ∈ Finset.Icc n m, ε j) * Hinf) * ind := by
    rw [Finset.sum_congr rfl fun j _ => hδ j]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [heq]
  have hmid : (∑ j ∈ Finset.Icc n m, Ah j) + (∑ j ∈ Finset.Icc n m, ε j) * Hinf
      ≤ Kh / (1 - r₂) + Se * Hinf := by
    have h := mul_le_mul_of_nonneg_right hSe hHinf
    linarith only [hhleg, h]
  have hmul := mul_le_mul_of_nonneg_right hmid hind0
  linarith only [hgleg, hmul]

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 2. `e.sum.delta.j.bound` at the concrete family, printed window -/

/-- **`e.sum.delta.j.bound`** at the `δ_j`, on the manuscript's own window `[n,
m-1]`:

```text
   ∑_{j=n}^{m-1} δ_j
     ≤ K_g r₁/(1-r₁) + ( K_h r₂/(1-r₂) + S_ε · C‖∇h‖_{L^∞(□_m)} ) 1_{z∉□_{m-1}} ,
```

`K_g = C·4·3^{m/2}σ̄_m^{-1}[g]`, `K_h = C·3^{m/2}[∇h]`, `r₁ = 3^{-(1/2-γ)}`,
`r₂ = 3^{-1/2}`. -/
theorem sum_Icc_stepFiveDelta_le {M : ABKModel d} {m0 : ℤ} {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {C : ℝ} (hC : 0 ≤ C) {gflux gradh : Vec d → E}
    {z : Vec d} {delta : ℝ} {omega : Cutoff.CutoffSample d} {n m : ℤ}
    (hnm : n ≤ m) (hm : m ≤ m0) {Se : ℝ}
    (hSe : ∑ j ∈ Finset.Icc n m, stepFiveEps M j z delta omega ≤ Se) :
    ∑ j ∈ Finset.Icc n (m - 1), stepFiveDelta M C m z gflux gradh delta omega j ≤
      stepFiveKg M C m gflux * stepFiveRatioG M / (1 - stepFiveRatioG M) +
        (stepFiveKh C m gradh * stepFiveRatioH / (1 - stepFiveRatioH) +
            Se * (C * stepFiveLinftyNorm m gradh)) * stepFiveBoundaryIndicator z m :=
  sum_Icc_delta_le_of_legs
    (δ := fun j => stepFiveDelta M C m z gflux gradh delta omega j)
    (Ag := fun j => stepFiveDeltaGLeg M C m gflux j)
    (Ah := fun j => stepFiveDeltaHLeg C m gradh j)
    (ε := fun j => stepFiveEps M j z delta omega)
    hnm (stepFiveRatioG_pos M) (stepFiveRatioG_lt_one hgamma) stepFiveRatioH_pos
    stepFiveRatioH_lt_one (stepFiveDeltaGLeg_nonneg hC M m gflux m)
    (fun _ hj => stepFiveDeltaGLeg_le_zpow hS hC hj hm)
    (stepFiveDeltaHLeg_nonneg hC m gradh m)
    (fun j _ => stepFiveDeltaHLeg_le_zpow C m gradh j)
    (fun j _ _ => stepFiveEps_nonneg M j z delta omega) hSe
    (mul_nonneg hC (stepFiveLinftyNorm_nonneg m gradh))
    (stepFiveBoundaryIndicator_nonneg z m)
    (fun j => stepFiveDelta_eq_legs M C m z gflux gradh delta omega j)

/-- **`e.sum.delta.j.bound` in the printed shape** — the same bound with the
coefficients written out, so that the pairing demands is visible: the `[g]`
slot carries `3^{m/2}σ̄_m^{-1}`, the `[∇h]` slot carries `3^{m/2}` alone, and
the boundary slot carries `S_ε ‖∇h‖_{L^∞(□_m)}`. -/
theorem sum_Icc_stepFiveDelta_le_print {M : ABKModel d} {m0 : ℤ} {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {C : ℝ} (hC : 0 ≤ C) {gflux gradh : Vec d → E}
    {z : Vec d} {delta : ℝ} {omega : Cutoff.CutoffSample d} {n m : ℤ}
    (hnm : n ≤ m) (hm : m ≤ m0) {Se : ℝ}
    (hSe : ∑ j ∈ Finset.Icc n m, stepFiveEps M j z delta omega ≤ Se) :
    ∑ j ∈ Finset.Icc n (m - 1), stepFiveDelta M C m z gflux gradh delta omega j ≤
      (4 * C * stepFiveRatioG M / (1 - stepFiveRatioG M)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) * ((Annealed.sigmaBar M m : ℝ))⁻¹ *
            stepFiveHalfSeminorm m gflux) +
        ((C * stepFiveRatioH / (1 - stepFiveRatioH)) *
              ((3 : ℝ) ^ ((m : ℝ) / 2) * stepFiveHalfSeminorm m gradh) +
            C * Se * stepFiveLinftyNorm m gradh) * stepFiveBoundaryIndicator z m := by
  refine (sum_Icc_stepFiveDelta_le hS hgamma hC hnm hm hSe).trans (le_of_eq ?_)
  simp only [stepFiveKg, stepFiveKh]
  ring

/-! ## 3. The anchor's window, and the `dataG` / `dataH` slots -/

/-- **`dataG`**: the `g`-half of `e.sum.delta.j.bound` on the anchor's window,
`C·4·3^{m/2}σ̄_m^{-1}[g] / (1 - 3^{-(1/2-γ)})`. -/
def stepFiveDataG (M : ABKModel d) (C : ℝ) (m : ℤ) (gflux : Vec d → E) : ℝ :=
  stepFiveKg M C m gflux / (1 - stepFiveRatioG M)

def stepFiveDataH (C : ℝ) (m : ℤ) (z : Vec d) (gradh : Vec d → E) (Se : ℝ) : ℝ :=
  (stepFiveKh C m gradh / (1 - stepFiveRatioH) + Se * (C * stepFiveLinftyNorm m gradh)) *
    stepFiveBoundaryIndicator z m

theorem stepFiveDataG_nonneg {M : ABKModel d} (hgamma : M.gamma < 1 / 2) {C : ℝ}
    (hC : 0 ≤ C) (m : ℤ) (gflux : Vec d → E) : 0 ≤ stepFiveDataG M C m gflux := by
  have h1 : (0 : ℝ) < 1 - stepFiveRatioG M := by
    linarith only [stepFiveRatioG_lt_one hgamma]
  exact div_nonneg (stepFiveKg_nonneg hC M m gflux) h1.le

theorem stepFiveDataH_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℤ) (z : Vec d)
    (gradh : Vec d → E) {Se : ℝ} (hSe : 0 ≤ Se) : 0 ≤ stepFiveDataH C m z gradh Se := by
  have h1 : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have h2 : 0 ≤ stepFiveKh C m gradh / (1 - stepFiveRatioH) :=
    div_nonneg (stepFiveKh_nonneg hC m gradh) h1.le
  have h3 : 0 ≤ Se * (C * stepFiveLinftyNorm m gradh) :=
    mul_nonneg hSe (mul_nonneg hC (stepFiveLinftyNorm_nonneg m gradh))
  rw [stepFiveDataH]
  exact mul_nonneg (by linarith only [h2, h3]) (stepFiveBoundaryIndicator_nonneg z m)

/-- **`e.sum.delta.j.bound` on the anchor's window** `Finset.Icc n m`, packaged
exactly for's `dataG` / `dataH` slots:

```text
   ∑_{j=n}^{m} δ_j  ≤  dataG + dataH .
```

Deviation D1 (the anchor sums one scale further than the print) is paid here by
the coefficient `1/(1-r)` in place of the printed `r/(1-r)`. -/
theorem sum_Icc_top_stepFiveDelta_le {M : ABKModel d} {m0 : ℤ} {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {C : ℝ} (hC : 0 ≤ C) {gflux gradh : Vec d → E}
    {z : Vec d} {delta : ℝ} {omega : Cutoff.CutoffSample d} {n m : ℤ}
    (hnm : n ≤ m) (hm : m ≤ m0) {Se : ℝ}
    (hSe : ∑ j ∈ Finset.Icc n m, stepFiveEps M j z delta omega ≤ Se) :
    ∑ j ∈ Finset.Icc n m, stepFiveDelta M C m z gflux gradh delta omega j ≤
      stepFiveDataG M C m gflux + stepFiveDataH C m z gradh Se := by
  rw [stepFiveDataG, stepFiveDataH]
  exact sum_Icc_top_delta_le_of_legs
    (δ := fun j => stepFiveDelta M C m z gflux gradh delta omega j)
    (Ag := fun j => stepFiveDeltaGLeg M C m gflux j)
    (Ah := fun j => stepFiveDeltaHLeg C m gradh j)
    (ε := fun j => stepFiveEps M j z delta omega)
    hnm (stepFiveRatioG_pos M) (stepFiveRatioG_lt_one hgamma) stepFiveRatioH_pos
    stepFiveRatioH_lt_one (stepFiveDeltaGLeg_nonneg hC M m gflux m)
    (fun _ hj => stepFiveDeltaGLeg_le_zpow hS hC hj hm)
    (stepFiveDeltaHLeg_nonneg hC m gradh m)
    (fun j _ => stepFiveDeltaHLeg_le_zpow C m gradh j) hSe
    (mul_nonneg hC (stepFiveLinftyNorm_nonneg m gradh))
    (stepFiveBoundaryIndicator_nonneg z m)
    (fun j => stepFiveDelta_eq_legs M C m z gflux gradh delta omega j)

end

end Algsuperdiff.Section4.Provider.Regularity
