/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepFiveBudgetSums

/-!
# `t.regularity` Step 4: the `ε_j` leg of the collapse

## The target

```text
   𝓔_{s/8,∞,2}(z + □_{n+1}; 𝐚_L − (κ_L − κ_{n+1})_{…}, σ̄_{n+1})
      =  Support.fluxCorrectedErrorRepresentative M L (n+1) ⟨s/8⟩ (τ_z ω) ,
```

while the Step-5 slot `ε_j` (`StepFiveBudgetSums.stepFiveEps`) is the `sup_{L ≥
j}` observable, restricted to the good event and pushed through `ENNReal.toReal`.

## Two exact alignments, and one shift

* **The gate is literally the same set.**  The excess-decay supply event is
  `goodEventAt M (cgEllipLowerConstant d) (n-2+3) z ⟨s/8⟩ (s/8 · √δ)` and
  `ε_j`'s indicator is
  `goodEventAt M (cgEllipLowerConstant d) j z ⟨s_8⟩ (stepOneEp δ)` with
  `stepOneEp δ = s_8 · √δ` and `s_8 = 1/32`.  At the Step-1 pin `s = 1/4` the
  two are the SAME term, constant for constant.
* **The observable is the same carrier**, and the per-level representative is
  dominated by the `sup_{L ≥ j}` observable
  (`Support.le_fluxCorrectedErrorObservableSup`) for every `L ≥ j`.
* **The scale shifts by one.**  The excess-decay display contracts the excess
  between scales `n` and `n-k`, but reads its error observable at `n-2+3 =
  n+1`.  Identifying the Step-5 index `j:= n` (which is what the excess indices
  force) therefore pins the Step-5 `ε`-slot at the shifted family `ε_{j+1}`, named
  `stepFourEps` below.  The shift is carried explicitly, not absorbed:
  `sum_Icc_stepFourEps_le` re-derives `e.sum.eps.j.bound` for it, at the same
  constant, from `GoodScaleWindows` on the shifted window `[n+1, m+1]`.

## The `toReal` corner, closed

`stepFiveEps` is a `toReal`, so a `⊤` observable would silently collapse the
slot to `0` and make the conversion.

## References

* ABK26, `t.regularity` Step 1; Step 4.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal
open scoped Classical

variable {d : ℕ}

/-! ## 1. The per-level representative under the Step-5 slot -/

/-- **The `ε_j` leg producer.**  On the good event, and with the observable
finite (the real cap `hcap`), the excess-decay lane's per-level flux-corrected
error at any truncation level `L ≥ j` is at most the Step-5 slot `ε_j`.

This is the exact conversion the Step-4 collapse needs: it turns the  leg datum
into the  `ε_j` at constant `1`. -/
theorem fluxCorrectedErrorRepresentative_le_stepFiveEps {M : ABKModel d} {j L : ℤ}
    {z : Vec d} {delta B : ℝ} {omega : Cutoff.CutoffSample d} (hjL : j ≤ L)
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) j z ⟨stepOneSEighth, stepOneSEighth_pos⟩
      (stepOneEp delta))
    (hcap : stepOneEpsJ M j z delta omega ≤ ENNReal.ofReal B) :
    Support.fluxCorrectedErrorRepresentative M L j
        ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) ≤
      stepFiveEps M j z delta omega := by
  have hval : stepOneEpsJ M j z delta omega =
      Support.fluxCorrectedErrorObservableSup M j
        ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) := by
    rw [stepOneEpsJ, Set.indicator_of_mem hmem]
  have hle := Support.le_fluxCorrectedErrorObservableSup M j
    ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) hjL
  have hne : stepOneEpsJ M j z delta omega ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap
  have hstep : ENNReal.ofReal
      (Support.fluxCorrectedErrorRepresentative M L j
        ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega)) ≤
      stepOneEpsJ M j z delta omega := by
    rw [hval]
    exact hle
  have htoReal := ENNReal.toReal_mono hne hstep
  rwa [ENNReal.toReal_ofReal
    (Support.fluxCorrectedErrorRepresentative_nonneg M L j
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega))]
    at htoReal

/-- The real-valued form of the `ε_j` cap: a `ℝ≥0∞` cap at a nonnegative real
transfers through `toReal`. -/
theorem stepFiveEps_le_of_cap {M : ABKModel d} {j : ℤ} {z : Vec d} {delta B : ℝ}
    {omega : Cutoff.CutoffSample d} (hB : 0 ≤ B)
    (hcap : stepOneEpsJ M j z delta omega ≤ ENNReal.ofReal B) :
    stepFiveEps M j z delta omega ≤ B :=
  ENNReal.toReal_le_of_le_ofReal hB hcap

/-- **The `ε_j` leg producer, under the annular anchor's own binders.**  The
finiteness datum is discharged from the proved a.e. cap `ae_stepOneEpsJ_le`,
whose constant `C_ann` is the frozen `annular_decomposition`'s; nothing else is
assumed. -/
theorem ae_fluxCorrectedErrorRepresentative_le_stepFiveEps (d : ℕ) :
    ∃ Cann : ℝ, 0 < Cann ∧
      ∀ M : ABKModel d, M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ 1 / 256 →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ (j : ℤ) (z : Vec d),
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                    (Support.cgEllipLowerConstant d) j z
                    ⟨stepOneSEighth, stepOneSEighth_pos⟩ (stepOneEp delta) →
                  ∀ L : ℤ, j ≤ L →
                    Support.fluxCorrectedErrorRepresentative M L j
                        ⟨stepOneSEighth, stepOneSEighth_pos⟩
                        (Cutoff.translateCutoffSample z omega) ≤
                      stepFiveEps M j z delta omega := by
  obtain ⟨Cann, hCann, hcap⟩ := ae_stepOneEpsJ_le d
  refine ⟨Cann, hCann, ?_⟩
  intro M hregime hgamma delta hdelta hsmall j z
  filter_upwards [hcap M hregime hgamma delta hdelta hsmall j z] with omega homega
  intro hmem L hjL
  exact fluxCorrectedErrorRepresentative_le_stepFiveEps hjL hmem homega

/-! ## 2. The index-shifted `ε`-family and its budget -/

/-- **The Step-4 `ε`-family**: the Step-5 slot read at the excess-decay lane's own
gate scale `j + 1` (see the module docstring). -/
noncomputable def stepFourEps (M : ABKModel d) (j : ℤ) (z : Vec d) (delta : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  stepFiveEps M (j + 1) z delta omega

theorem stepFourEps_nonneg (M : ABKModel d) (j : ℤ) (z : Vec d) (delta : ℝ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ stepFourEps M j z delta omega :=
  stepFiveEps_nonneg M (j + 1) z delta omega

/-- Re-indexing a sum over `[n,m]` by the unit shift. -/
theorem sum_Icc_shift_one (f : ℤ → ℝ) (n m : ℤ) :
    ∑ j ∈ Finset.Icc n m, f (j + 1) = ∑ k ∈ Finset.Icc (n + 1) (m + 1), f k := by
  have hset : Finset.Icc (n + 1) (m + 1) = (Finset.Icc n m).image fun j => j + 1 := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro hk
      exact ⟨k - 1, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hset, Finset.sum_image (by
    intro x _ y _ hxy
    have hxy' : x + 1 = y + 1 := hxy
    omega)]

/-- **`e.sum.eps.j.bound` for the shifted family** (the price of the index
shift is nil): from `GoodScaleWindows` on `[n+1, m+1]`,

```text
   ∑_{j=n}^{m} ε_{j+1}(z)  ≤  δ ((m-n) + 1) ,          z = 3^n v .
```

The centre is the SAME lattice point `3^n v` the Step-5 chain carries: the
shifted window's own "fine" lattice `3^{(n+1)-1}ℤ^d` is exactly `3^n ℤ^d`. -/
theorem sum_Icc_stepFourEps_le {M : ABKModel d} {delta : ℝ} {n m : ℤ}
    {omega : Cutoff.CutoffSample d} (hdelta : 0 ≤ delta)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos (n + 1) (m + 1)
      omega)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n (m + 1)) :
    ∑ j ∈ Finset.Icc n m,
        stepFourEps M j (Support.triadicLatticePoint n v) delta omega ≤
      delta * (((m - n).toNat : ℝ) + 1) := by
  have hidx : n + 1 - 1 = n := by omega
  have hv' : v ∈ Support.latticeCubeSet d (n + 1 - 1) (m + 1) := by
    rw [hidx]
    exact hv
  have h := sum_stepFiveEps_le_of_goodScaleWindows_fine (M := M) (delta := delta)
    (n := n + 1) (m := m + 1) (omega := omega) hdelta hgood hv'
  rw [hidx] at h
  have hlen : ((m + 1 - (n + 1)).toNat : ℝ) = ((m - n).toNat : ℝ) := by
    congr 2
    omega
  rw [hlen] at h
  rw [show (fun j : ℤ => stepFourEps M j (Support.triadicLatticePoint n v) delta omega) =
      fun j : ℤ => stepFiveEps M (j + 1) (Support.triadicLatticePoint n v) delta omega from
    rfl]
  rw [sum_Icc_shift_one
    (fun k => stepFiveEps M k (Support.triadicLatticePoint n v) delta omega) n m]
  exact h

end Algsuperdiff.Section4.Provider.Regularity
