/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFiveDeltaSum
import Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitLift

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization Algsuperdiff.Section4.Provider.ExcessDecay MeasureTheory
open scoped ENNReal
open scoped Classical

noncomputable section

variable {d : ℕ}

/-! ## 1. The window average of `∇h`, and its cap -/

/-- **The window average is capped by any pointwise bound on the domain cube.**

`‖(∇h)_W‖ ≤ K` whenever `‖∇h‖ ≤ K` pointwise on `□_m ⊇ W`.  This is the `|avg
∇h| ≤ ‖∇h‖_{L^∞}` step the boundary chain uses, taken at the pointwise binder
rather than at an essential supremum. -/
theorem norm_volumeAverageVec_truncatedWindow_le_of_bound {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) {gradh : Vec d → Vec d} {K : ℝ}
    (hK : 0 ≤ K)
    (hint : ∀ i, IntegrableOn (fun y => gradh y i) (truncatedWindow z m j) volume)
    (hbd : ∀ y ∈ openCubeSet (originCube d m), ‖gradh y‖ ≤ K) :
    ‖volumeAverageVec (truncatedWindow z m j) gradh‖ ≤ K := by
  have hsub := norm_volumeAverageVec_sub_le (W := truncatedWindow z m j) (G := gradh)
    (A := 0) (K := K) (volume_truncatedWindow_pos j hz)
    (volume_truncatedWindow_lt_top z m j) hint hK
    (fun y hy => by
      simpa using hbd y (truncatedWindow_subset_domain z m j hy))
  simpa using hsub

/-! ## 2. The `ε`-free average leg -/

/-- **The `ε`-free average leg of the boundary `δ_j`** -- the anchor's fifth leg
after the excess normalizer, at the anchor's own window `n+2`:

```text
   C ‖(∇h)_{(z+□_{j+2})∩□_m}‖ .
```

in `j`: no geometric ratio, no `ε`. -/
def stepFiveFlatAvgLeg (C : ℝ) (m : ℤ) (z : Vec d) (gradh : Vec d → Vec d) (j : ℤ) : ℝ :=
  C * ‖volumeAverageVec (truncatedWindow z m (j + 2)) gradh‖

theorem stepFiveFlatAvgLeg_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℤ) (z : Vec d)
    (gradh : Vec d → Vec d) (j : ℤ) : 0 ≤ stepFiveFlatAvgLeg C m z gradh j :=
  mul_nonneg hC (norm_nonneg _)

/-- The uniform cap of the `ε`-free leg, at a pointwise bound for `∇h` on `□_m`. -/
theorem stepFiveFlatAvgLeg_le {C : ℝ} (hC : 0 ≤ C) {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) {gradh : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hint : ∀ i, IntegrableOn (fun y => gradh y i) (truncatedWindow z m (j + 2)) volume)
    (hbd : ∀ y ∈ openCubeSet (originCube d m), ‖gradh y‖ ≤ K) :
    stepFiveFlatAvgLeg C m z gradh j ≤ C * K :=
  mul_le_mul_of_nonneg_left
    (norm_volumeAverageVec_truncatedWindow_le_of_bound hz hK hint hbd) hC

/-! ## 3. The boundary `δ_j`, and its window sum -/

/-- **The boundary `δ_j`**: the print's family the anchor's `ε`-free average leg,
the whole `∇h` half gated by `1_{z ∉ □_{m-1}}`. -/
def stepFiveDeltaBoundary (M : ABKModel d) (C : ℝ) (m : ℤ) (z : Vec d)
    (gflux gradh : Vec d → Vec d) (delta : ℝ) (omega : Cutoff.CutoffSample d) (j : ℤ) : ℝ :=
  stepFiveDelta M C m z gflux gradh delta omega j +
    stepFiveFlatAvgLeg C m z gradh j * stepFiveBoundaryIndicator z m

theorem stepFiveDeltaBoundary_nonneg {C : ℝ} (hC : 0 ≤ C) (M : ABKModel d) (m : ℤ)
    (z : Vec d) (gflux gradh : Vec d → Vec d) (delta : ℝ)
    (omega : Cutoff.CutoffSample d) (j : ℤ) :
    0 ≤ stepFiveDeltaBoundary M C m z gflux gradh delta omega j := by
  rw [stepFiveDeltaBoundary]
  have h1 := stepFiveDelta_nonneg hC M m z gflux gradh delta omega j
  have h2 : 0 ≤ stepFiveFlatAvgLeg C m z gradh j * stepFiveBoundaryIndicator z m :=
    mul_nonneg (stepFiveFlatAvgLeg_nonneg hC m z gradh j)
      (stepFiveBoundaryIndicator_nonneg z m)
  linarith only [h1, h2]

/-- **`dataH` on the boundary branch**, the three `∇h` legs summed:

```text
   dataH_∂ = ( K_h/(1-r₂) + S_ε C‖∇h‖_{L^∞} + W · C K_flat ) 1_{z∉□_{m-1}} ,
```

with `W` the window count `(m-n+1)` and `K_flat` a uniform cap for the anchor's
window averages.  The third summand is the `ε`-free one: it is `W`-linear and
carries no `(1-α)`. -/
def stepFiveDataHBoundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ℝ) (m : ℤ) (z : Vec d) (gradh : Vec d → E) (Se W Kflat : ℝ) : ℝ :=
  (stepFiveKh C m gradh / (1 - stepFiveRatioH) + Se * (C * stepFiveLinftyNorm m gradh) +
      W * (C * Kflat)) * stepFiveBoundaryIndicator z m

theorem stepFiveDataHBoundary_nonneg {C : ℝ} (hC : 0 ≤ C) (m : ℤ) (z : Vec d)
    (gradh : Vec d → Vec d) {Se W Kflat : ℝ} (hSe : 0 ≤ Se) (hW : 0 ≤ W)
    (hKflat : 0 ≤ Kflat) : 0 ≤ stepFiveDataHBoundary C m z gradh Se W Kflat := by
  have h1 : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have h2 : 0 ≤ stepFiveKh C m gradh / (1 - stepFiveRatioH) :=
    div_nonneg (stepFiveKh_nonneg hC m gradh) h1.le
  have h3 : 0 ≤ Se * (C * stepFiveLinftyNorm m gradh) :=
    mul_nonneg hSe (mul_nonneg hC (stepFiveLinftyNorm_nonneg m gradh))
  have h4 : 0 ≤ W * (C * Kflat) := mul_nonneg hW (mul_nonneg hC hKflat)
  rw [stepFiveDataHBoundary]
  exact mul_nonneg (by linarith only [h2, h3, h4]) (stepFiveBoundaryIndicator_nonneg z m)

/-- The `ε`-free leg's window sum: `(m-n+1)` copies of its uniform cap. -/
theorem sum_Icc_stepFiveFlatAvgLeg_le {C : ℝ} (hC : 0 ≤ C) {m n : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) {gradh : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hnm : n ≤ m)
    (hint : ∀ j : ℤ, ∀ i, IntegrableOn (fun y => gradh y i)
      (truncatedWindow z m (j + 2)) volume)
    (hbd : ∀ y ∈ openCubeSet (originCube d m), ‖gradh y‖ ≤ K) :
    ∑ j ∈ Finset.Icc n m, stepFiveFlatAvgLeg C m z gradh j ≤
      (((m : ℝ) - (n : ℝ)) + 1) * (C * K) := by
  have hcard : (Finset.Icc n m).card = (m + 1 - n).toNat := Int.card_Icc n m
  have hbound : ∑ j ∈ Finset.Icc n m, stepFiveFlatAvgLeg C m z gradh j ≤
      ((Finset.Icc n m).card : ℝ) * (C * K) := by
    have h := Finset.sum_le_card_nsmul (Finset.Icc n m)
      (fun j => stepFiveFlatAvgLeg C m z gradh j) (C * K)
      (fun j _ => stepFiveFlatAvgLeg_le hC hz hK (hint j) hbd)
    simpa [nsmul_eq_mul] using h
  have hcardR : ((Finset.Icc n m).card : ℝ) = ((m : ℝ) - (n : ℝ)) + 1 := by
    rw [hcard]
    have : ((m + 1 - n).toNat : ℤ) = m + 1 - n := Int.toNat_of_nonneg (by omega)
    have hcast : (((m + 1 - n).toNat : ℤ) : ℝ) = ((m + 1 - n : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) this
    push_cast at hcast ⊢
    linarith only [hcast]
  rw [hcardR] at hbound
  exact hbound

/-- **The boundary `δ`-budget** (`e.sum.delta.j.bound` with the anchor's
`ε`-free leg carried), on the iteration anchor's window `Icc n m`:

```text
   ∑_{j=n}^{m} δ_j^∂  ≤  dataG + dataH_∂ ,
```

`dataH_∂` as above at `W = (m-n+1)`. -/
theorem sum_Icc_top_stepFiveDeltaBoundary_le {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {C : ℝ} (hC : 0 ≤ C) {gflux gradh : Vec d → Vec d}
    {z : Vec d} {delta : ℝ} {omega : Cutoff.CutoffSample d} {n m : ℤ} (hnm : n ≤ m)
    (hm : m ≤ m0) (hz : z ∈ openCubeSet (originCube d m)) {Se K : ℝ} (hK : 0 ≤ K)
    (hSe : ∑ j ∈ Finset.Icc n m, stepFiveEps M j z delta omega ≤ Se)
    (hint : ∀ j : ℤ, ∀ i, IntegrableOn (fun y => gradh y i)
      (truncatedWindow z m (j + 2)) volume)
    (hbd : ∀ y ∈ openCubeSet (originCube d m), ‖gradh y‖ ≤ K) :
    ∑ j ∈ Finset.Icc n m, stepFiveDeltaBoundary M C m z gflux gradh delta omega j ≤
      stepFiveDataG M C m gflux +
        stepFiveDataHBoundary C m z gradh Se (((m : ℝ) - (n : ℝ)) + 1) K := by
  have hprint := sum_Icc_top_stepFiveDelta_le (E := Vec d) (gflux := gflux) (gradh := gradh)
    hS hgamma hC hnm hm hSe
  have hflat := sum_Icc_stepFiveFlatAvgLeg_le hC hz hK hnm hint hbd
  have hsplit : ∑ j ∈ Finset.Icc n m, stepFiveDeltaBoundary M C m z gflux gradh delta omega j
      = (∑ j ∈ Finset.Icc n m, stepFiveDelta M C m z gflux gradh delta omega j) +
        (∑ j ∈ Finset.Icc n m, stepFiveFlatAvgLeg C m z gradh j) *
          stepFiveBoundaryIndicator z m := by
    simp only [stepFiveDeltaBoundary, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hindnn : 0 ≤ stepFiveBoundaryIndicator z m := stepFiveBoundaryIndicator_nonneg z m
  have hflatmul := mul_le_mul_of_nonneg_right hflat hindnn
  have hexpand : stepFiveDataHBoundary C m z gradh Se (((m : ℝ) - (n : ℝ)) + 1) K =
      stepFiveDataH C m z gradh Se +
        ((((m : ℝ) - (n : ℝ)) + 1) * (C * K)) * stepFiveBoundaryIndicator z m := by
    simp only [stepFiveDataHBoundary, stepFiveDataH]
    ring
  rw [hsplit, hexpand]
  linarith only [hprint, hflatmul]

end

end Algsuperdiff.Section4.Provider.Regularity
