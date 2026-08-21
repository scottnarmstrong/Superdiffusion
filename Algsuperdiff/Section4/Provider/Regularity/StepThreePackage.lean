/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepThreeBudget
import Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows

/-!
# `t.regularity` Step 3, assembled: one a.e. statement carrying the windows,
# the bad-scale budget, the separation, and the `ε_j(z)` caps

## What is delivered

`stepThree_windowsAndBadBudget` is ABK26 `t.regularity` Step 3 as ONE theorem,
on top's `stepOne_parameterWeb`: for every dimension `d`, every `c⋆ > 0` and
the two abstract `d`-constants `(C_edos ≥ 1, C_iter)` it produces the Step-1
constant `C₁`, the regime threshold `γ₀` and the `α`-range constant `C`, and
then, for every model in the regime, every `α` in the range and every `m`, a
minimal scale `Z` such that `X := Z + k + 3` is measurable with the anchor's
printed tail, and **almost surely**:

1. the `ε_j(z)` cap of Step 1 holds simultaneously at every scale `j` and every
   triadic lattice centre (a countable family, so the caps — one null set per
   `(j, z)` — merge into a single null set);
2. at every window `[n, m]` on which the `X`-gate `X ω ≤ m - n` holds, the
   window is at least 14 scales long, and for printed centre `z ∈ 3^n ℤ^d ∩
   □_m` simultaneously:
   * `U_j := (z + □_j) ∩ □_m` is an admissible iteration-lemma family
     (`IterationWindowFamily`: measurable, nested, sandwiched);
   * `𝓑_z ⊆ [n, m]`, the iteration lemma's `B`-binder;
   * `|𝓑_z| ≤ δ(m - n + 1)`, `e.bad.scale.proportion.bound`;
   * `|𝓑_z| + 7 ≤ m - n`, the separation.

Items 1--2 are exactly what the Step-4 excess-decay application and the Step-5
iteration application read off Step 3.

## What is not formed here

The excess `E_j := E(u, U_j) = 3^{-j} min_ℓ ‖u - ℓ‖_{L̄²(U_j)}` and the optimal
affine functions `ℓ_j` are NOT formed: they are functions of the solution `u`,
which enters only with Step 4's excess-decay lemma, and the development already
carries their carriers (`Support.affineExcess`, `Support.IsAffineMinimizer`)
for the frozen iteration lemma.  Step 3's own content — the windows, the bad
set, the budget — is what this module delivers.  Nothing about `u`, `g`, `h`,
`L` or the truncated operator `a_L` appears here; the `L`-reconciliation gap is
untouched.

## References

* ABK26, `t.regularity` Steps 1--3.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open Homogenization MeasureTheory
open scoped ENNReal
open scoped Classical

variable {d : ℕ}

/-! ## 1. The per-window conclusion -/

/-- **The Step-3 conclusion at one window `[n, m]`**, uniformly over the printed
lattice centres `z ∈ 3^n ℤ^d ∩ □_m`: the window family is an admissible
iteration family, the bad set sits in the counting window, it obeys
`e.bad.scale.proportion.bound`, and it satisfies the separation. -/
def StepThreeWindowsAndBudget (M : ABKModel d) (delta : ℝ) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ v : Fin d → ℤ, v ∈ Support.latticeCubeSet d n m →
    IterationWindowFamily (stepThreeWindow (Support.triadicLatticePoint n v) m) m ∧
      stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega ⊆
        Finset.Icc n m ∧
      ((stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega).card : ℝ) ≤
        delta * (((m - n).toNat : ℝ) + 1) ∧
      StepOneBadSetSeparation
        (stepThreeBadSet M delta n m (Support.triadicLatticePoint n v) omega).card n m

/-- The per-window conclusion, from the producer's good-scales clause alone. -/
theorem stepThreeWindowsAndBudget_of_goodScaleWindows {M : ABKModel d} {delta : ℝ}
    {n m : ℤ} {omega : Cutoff.CutoffSample d} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / 2) (hwin : (14 : ℤ) ≤ m - n)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega) :
    StepThreeWindowsAndBudget M delta n m omega := by
  intro v hv
  refine ⟨iterationWindowFamily_stepThreeWindow _ m
      (mem_openCubeSet_of_mem_latticeCubeSet hv),
    stepThreeBadSet_subset_Icc M delta n m _ omega,
    stepThreeBadSet_card_le_of_goodScaleWindows hdelta0 hgood hv, ?_⟩
  exact stepOneBadSetSeparation_of_goodScaleWindows hdelta0 hdelta hwin hgood hv

/-! ## 2. The Step-3 endpoint -/

/-- **`t.regularity` Step 3: the windows and the bad-scale budget.**

See the module docstring for the four delivered items.  `C_edos` is the
abstract excess-decay one-step constant (floored at `1`, which is what
discharges the sharpened pin `k ≥ 11`), `C_iter` the abstract Step-6 iteration
constant; both are's, and the produced `(C₁, γ₀, C)` are's package verbatim. -/
theorem stepThree_windowsAndBadBudget (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar)
    (Cedos Citer : ℝ) (hCedos : 1 ≤ Cedos) :
    ∃ C1 gamma0 C : ℝ, 2 ≤ C1 ∧ 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ Z : Cutoff.CutoffSample d → ℕ∞,
            Measurable (minimalScaleX Z (stepOneK Cedos)) ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure
                    {omega | (N : ℕ∞) ≤ minimalScaleX Z (stepOneK Cedos) omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              (∀ (j nz : ℤ) (v : Fin d → ℤ),
                  stepOneEpsJ M j (Support.triadicLatticePoint nz v)
                      (stepOneDelta C1 alpha) omega ≤
                    ENNReal.ofReal
                      (1 / 2 * Real.rpow stepOneS (3 / 2 : ℝ) * Cedos⁻¹ *
                        Real.rpow (3 : ℝ) (-(stepOneK Cedos : ℝ) / 4))) ∧
              ∀ n : ℤ, n ≤ m →
                minimalScaleX Z (stepOneK Cedos) omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                  (14 : ℤ) ≤ m - n ∧
                  StepThreeWindowsAndBudget M (stepOneDelta C1 alpha) n m omega := by
  obtain ⟨C1, gamma0, C, hC1, _, _, hg0, _, hC, hweb⟩ :=
    stepOne_parameterWeb d cstar hcstar Cedos Citer hCedos
  refine ⟨C1, gamma0, C, hC1, hg0, hC, ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  obtain ⟨hdelta, _, hcap, hRG1⟩ := hweb M hcs hgamma alpha halpha0 halpha
  obtain ⟨Z, _, _, hXmeas, hXtail, hXgood⟩ := hRG1 m
  refine ⟨Z, hXmeas, hXtail, ?_⟩
  have hcaps : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (j nz : ℤ) (v : Fin d → ℤ),
        stepOneEpsJ M j (Support.triadicLatticePoint nz v) (stepOneDelta C1 alpha)
            omega ≤
          ENNReal.ofReal
            (1 / 2 * Real.rpow stepOneS (3 / 2 : ℝ) * Cedos⁻¹ *
              Real.rpow (3 : ℝ) (-(stepOneK Cedos : ℝ) / 4)) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro nz
    rw [ae_all_iff]
    intro v
    exact hcap j (Support.triadicLatticePoint nz v)
  filter_upwards [hcaps, hXgood] with omega hcapsw hgoodw
  refine ⟨hcapsw, ?_⟩
  intro n hn hgate
  have hwin : (14 : ℤ) ≤ m - n :=
    fourteen_le_window Z (eleven_le_stepOneK hCedos) omega hgate
  refine ⟨hwin, ?_⟩
  exact stepThreeWindowsAndBudget_of_goodScaleWindows (le_of_lt hdelta.1) hdelta.2 hwin
    (hgoodw n hn hgate)

end Algsuperdiff.Section4.Provider.Regularity
