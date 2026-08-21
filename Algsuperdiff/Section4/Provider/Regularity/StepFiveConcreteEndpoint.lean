/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFiveDeltaSum
import Algsuperdiff.Section4.Provider.Regularity.StepFiveIterationResult

/-!
# `t.regularity` Step 5: the concrete endpoint

## What this module is

`e.oscillation.iteration.result`
(`oscillationIterationResult_of_stepFourDecay`) is proved with `ε`, `δ`,
`dataG`, `dataH` as free slots, and the concrete `δ_j` family
(`StepFiveDeltaFamily`) and its summation (`StepFiveDeltaSum`) are proved
separately.  This module is the single composition: every slot is filled with
the printed object.  The only hypothesis that survives is Step 4's decay
hypothesis `hstep4`, quoted verbatim below.

Filled in from the proved material, none of it conditional:

* `ε := ε_j(z,ω)` = `stepFiveEps`, and its budget `∑_{Icc n m} ε_j ≤ 2 δ
  (m-n)` = the unconditional `e.sum.eps.j.bound`
  (`sum_stepFiveEps_le_two_mul_delta_mul_window`), discharged inside from
  `GoodScaleWindows` + the Step-3 window gate `14 ≤ m-n`;
* `δ := δ_j` = `stepFiveDelta`, with `0 ≤ δ_j` discharged inside;
* `dataG := stepFiveDataG`, `dataH := stepFiveDataH`, and
  `∑_{Icc n m} δ_j ≤ dataG + dataH` = `e.sum.delta.j.bound`
  (`sum_Icc_top_stepFiveDelta_le`), discharged inside from the frozen
  Section-3 `inductionState` alone.

## `toReal`, once more

The concrete `δ_j` is built through `ENNReal.toReal`.  As explained in
`StepFiveDeltaFamily`, that convention is inert in every inequality proved in
this tree; it is load-bearing only inside `hstep4`, whose supplier must present
Step 4's decay at the finite seminorm values — which the root's own `Kg`, `Kh`,
`KhInf` legs guarantee via the two bridge theorems of `StepFiveDeltaFamily`.

## References

* ABK26, `t.regularity` Step 5.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Step-5 concrete endpoint**: `e.sum.delta.j.bound` and
`e.oscillation.iteration.result` composed, with every slot concrete.

For every `n', m'` with `n ≤ n' ≤ m' ≤ m`,

```text
   3^{-n'} ‖u - (u)_{U_{n'}}‖_{L̲²(U_{n'})}
     ≤ C exp( C₁^{-1} C_iter (1-α)(m-n) ) ( 3^{-m'} ‖u - (u)_{U_{m'}}‖ + C·dataG )
       + C exp( C₁^{-1} C_iter (1-α)(m-n) ) · dataH ,
```

with

```text
   dataG = C_δ · 4 · 3^{m/2} σ̄_m^{-1} [g]_{W̲^{1/2,∞}(□_m)} / (1 - 3^{-(1/2-γ)}) ,
   dataH = ( C_δ · 3^{m/2} [∇h]_{W̲^{1/2,∞}(□_m)} / (1 - 3^{-1/2})
             + 2 δ (m-n) · C_δ ‖∇h‖_{L^∞(□_m)} ) · 1_{z ∉ □_{m-1}} ,
```

`δ = C₁^{-1}(1-α)`, `C₁ = stepOne d Cedos Cann C_iter k`, `z = 3^n v`.

```lean
   ∀ j : ℤ, n + (k : ℤ) ≤ j → j ≤ m - 1 → j ∉ Bz →
     affineExcess (U (j - (k : ℤ))) u ≤
       stepFiveTheta ^ k * affineExcess (U j) u +
         stepFiveEps M j (triadicLatticePoint n v)
             (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega *
           slopeMagnitude (slope j) +
         stepFiveDelta M Cdel m (triadicLatticePoint n v) gflux gradh
           (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega j
```

Every other hypothesis is a source premise or the standing Section-3 frame. -/
theorem stepFiveConcreteOscillationResult_of_stepFourDecay (d : ℕ) (hd : d ≠ 0) (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ C Citer : ℝ, 0 < C ∧ 0 ≤ Citer ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
      Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
      M.gamma < 1 / 2 →
      ∀ (Cedos Cann alpha : ℝ), alpha ≤ 1 →
      ∀ Cdel : ℝ, 0 ≤ Cdel →
      ∀ (gflux gradh : Vec d → E) (omega : Cutoff.CutoffSample d),
      ∀ n m : ℤ, (14 : ℤ) ≤ m - n → m ≤ m0 →
      GoodScaleWindows M stepOneSEighth
          (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha)
          stepOneSEighth_pos n m omega →
      ∀ v : Fin d → ℤ, v ∈ latticeCubeSet d n m →
      ∀ U : ℤ → Set (Vec d), IterationWindowFamily U m →
      ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (U m)) →
      ∀ (c : ℤ → ℝ) (slope : ℤ → Vec d),
      (∀ j : ℤ, j ≤ m → IsAffineMinimizer (U j) u (c j) (slope j)) →
      ∀ Bz : Finset ℤ,
      (Bz.card : ℝ) ≤
          stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha * (((m : ℝ) - (n : ℝ)) + 1) →
      (∀ j : ℤ, n + (k : ℤ) ≤ j → j ≤ m - 1 → j ∉ Bz →
        affineExcess (U (j - (k : ℤ))) u ≤
          stepFiveTheta ^ k * affineExcess (U j) u +
            stepFiveEps M j (triadicLatticePoint n v)
                (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega *
              slopeMagnitude (slope j) +
            stepFiveDelta M Cdel m (triadicLatticePoint n v) gflux gradh
              (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega j) →
      ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
        (3 : ℝ) ^ (-n') * normalizedL2On (U n') (fun x => u x - volumeAverage (U n') u) ≤
          C *
              Real.exp
                ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
              ((3 : ℝ) ^ (-m') *
                  normalizedL2On (U m') (fun x => u x - volumeAverage (U m') u) +
                C * stepFiveDataG M Cdel m gflux) +
            C *
              Real.exp
                ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer * stepSixExponent alpha n m) *
              stepFiveDataH Cdel m (triadicLatticePoint n v) gradh
                (2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
                  ((m : ℝ) - (n : ℝ))) := by
  obtain ⟨C, Citer, hC, hCiter, hmain⟩ := oscillationIterationResult_of_stepFourDecay d hd k hk
  refine ⟨C, Citer, hC, hCiter, ?_⟩
  intro M m0 Ecap hS hgamma Cedos Cann alpha halpha Cdel hCdel gflux gradh omega n m hwin
    hm0 hgood v hv U hU u hu c slope hmin Bz hBz hstep4 n' m' hn' hn'm' hm'm
  have hnm : n ≤ m := by omega
  have hC1pos : 0 < stepOneC1 d Cedos Cann Citer k := stepOneC1_pos d Cedos Cann Citer k
  have hdelta : 0 ≤ stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha := by
    simp only [stepOneDelta]
    exact mul_nonneg (inv_nonneg.mpr hC1pos.le) (by linarith only [halpha])
  have hmnR : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have hcast : ((n : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := Int.cast_le.mpr hnm
    linarith only [hcast]
  have hSe := sum_stepFiveEps_le_two_mul_delta_mul_window hdelta hwin hgood hv
  have hSd := sum_Icc_top_stepFiveDelta_le (C := Cdel) (gflux := gflux) (gradh := gradh)
    hS hgamma hCdel hnm hm0 hSe
  have hSeNN : (0 : ℝ) ≤
      2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha * ((m : ℝ) - (n : ℝ)) := by
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdelta) hmnR
    linarith only [h]
  exact hmain Cedos Cann alpha halpha n m (by omega) U hU u hu c slope hmin Bz hBz
    (fun j =>
      stepFiveEps M j (triadicLatticePoint n v)
        (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega)
    (fun j =>
      stepFiveDelta M Cdel m (triadicLatticePoint n v) gflux gradh
        (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega j)
    (fun j _ _ =>
      stepFiveEps_nonneg M j (triadicLatticePoint n v)
        (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega)
    (fun j _ _ =>
      stepFiveDelta_nonneg hCdel M m (triadicLatticePoint n v) gflux gradh
        (stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha) omega j)
    hSe _ _ (stepFiveDataG_nonneg hgamma hCdel m gflux)
    (stepFiveDataH_nonneg hCdel m (triadicLatticePoint n v) gradh hSeNN) hSd hstep4
    n' m' hn' hn'm' hm'm

end

end Algsuperdiff.Section4.Provider.Regularity
