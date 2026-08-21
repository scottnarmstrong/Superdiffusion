/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.StepSevenSelectionPackage
import Algsuperdiff.Section4.Provider.Regularity.StepThreePackage

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The shifted candidate range -/

/-- **The shifted Step-7a candidate range** `[n+4, m-3] ∩ ℤ`: the printed range
with its bottom scale removed, so that every member `j` has `j-1` still above
`n+2`. -/
def stepSevenShiftedCandidates (n m : ℤ) : Finset ℤ := Finset.Icc (n + 4) (m - 3)

theorem card_stepSevenShiftedCandidates (n m : ℤ) :
    (stepSevenShiftedCandidates n m).card = (m - n - 6).toNat := by
  rw [stepSevenShiftedCandidates, Int.card_Icc]
  congr 1
  ring

/-- The good scales of the shifted range. -/
def stepSevenShiftedGoodScales (B : Finset ℤ) (n m : ℤ) : Finset ℤ :=
  stepSevenShiftedCandidates n m \ B

theorem mem_stepSevenShiftedGoodScales_iff {B : Finset ℤ} {n m j : ℤ} :
    j ∈ stepSevenShiftedGoodScales B n m ↔ (n + 4 ≤ j ∧ j ≤ m - 3) ∧ j ∉ B := by
  rw [stepSevenShiftedGoodScales, Finset.mem_sdiff, stepSevenShiftedCandidates,
    Finset.mem_Icc]

/-- **Non-emptiness of the shifted range** under the separation
`|𝓑| + 7 ≤ m - n` — the same demand that funds the range for `n' < m'`. -/
theorem stepSevenShiftedGoodScales_nonempty {B : Finset ℤ} {n m : ℤ}
    (hsep : (B.card : ℤ) + 7 ≤ m - n) :
    (stepSevenShiftedGoodScales B n m).Nonempty := by
  have hunion : (stepSevenShiftedGoodScales B n m).card + B.card =
      (stepSevenShiftedCandidates n m ∪ B).card :=
    Finset.card_sdiff_add_card _ _
  have hle : (stepSevenShiftedCandidates n m).card ≤
      (stepSevenShiftedCandidates n m ∪ B).card :=
    Finset.card_le_card Finset.subset_union_left
  have hcard := card_stepSevenShiftedCandidates n m
  refine Finset.card_pos.mp ?_
  omega

/-! ## 2. The shifted selection, with its sharp gap -/

/-- **The shifted good scale exists, with the sharp gap.**

From the proved separation alone: a scale `j ∈ [n+4, m-3]` outside the bad set,
whose distance from `n` is bounded by `|𝓑| + 4` — one unit sharper than the
printed `|𝓑| + 6` the chain's `hgap` slot asks of `j - 1`. -/
theorem exists_shiftedGoodScale {B : Finset ℤ} {n m : ℤ}
    (hsep : (B.card : ℤ) + 7 ≤ m - n) :
    ∃ j : ℤ, n + 4 ≤ j ∧ j ≤ m - 3 ∧ j ∉ B ∧ j - n ≤ (B.card : ℤ) + 4 := by
  have hne := stepSevenShiftedGoodScales_nonempty (B := B) (n := n) (m := m) hsep
  set S := stepSevenShiftedGoodScales B n m with hS
  set j := S.min' hne with hj
  have hjmem := mem_stepSevenShiftedGoodScales_iff.mp (S.min'_mem hne)
  refine ⟨j, hjmem.1.1, hjmem.1.2, hjmem.2, ?_⟩
  have hsub : Finset.Ico (n + 4) j ⊆ B := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    by_contra hiB
    have hiS : i ∈ S :=
      mem_stepSevenShiftedGoodScales_iff.mpr
        ⟨⟨hi.1, by linarith only [hi.2, hjmem.1.2]⟩, hiB⟩
    have := S.min'_le i hiS
    omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Ico] at hcard
  have hlo := hjmem.1.1
  omega

/-! ## 3. The Step-3 instantiation: the good at the shifted scale -/

/-- **The Caccioppoli's cube scale, at the Step-3 bad set.**

At every printed lattice centre `z`'s `StepThreeWindowsAndBudget` delivers the
separation, and the shifted pigeonhole turns it into a scale `j` whose GOOD
membership holds at `ω` — which is exactly the gate of
`StepSevenLambdaGoodEvent.ae_stepSevenLambdaCaps` at `k = j`.  Setting the
chain's free lower scale to `n' := j - 1` makes the payload's `capsCacc` cube
`□_{n'+1}` equal to `□_j`. -/
theorem exists_capsCaccScale {M : ABKModel d} {delta : ℝ} {n m : ℤ}
    {omega : Cutoff.CutoffSample d}
    (hbudget : StepThreeWindowsAndBudget M delta n m omega) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) :
    ∃ j : ℤ, n + 4 ≤ j ∧ j ≤ m - 3 ∧
      j - n ≤ ((stepThreeBadSet M delta n m
        (Support.triadicLatticePoint n v) omega).card : ℤ) + 4 ∧
      omega ∈ stepThreeGoodEvent M delta j (Support.triadicLatticePoint n v) := by
  obtain ⟨-, -, -, hsep⟩ := hbudget v hv
  rw [StepOneBadSetSeparation] at hsep
  obtain ⟨j, hlo, hhi, hjB, hgap⟩ := exists_shiftedGoodScale hsep
  exact ⟨j, hlo, hhi, hgap,
    mem_stepThreeGoodEvent_of_notMem_stepThreeBadSet (by omega) (by omega) hjB⟩

end

end Algsuperdiff.Section4.Provider.Regularity
