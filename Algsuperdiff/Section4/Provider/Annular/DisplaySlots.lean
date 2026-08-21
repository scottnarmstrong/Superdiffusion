/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.RepresentativeTransfer
import Algsuperdiff.Section4.Provider.Proportion.LatticeCount

/-!
# The two lattice slots of the clause-(i) representative display

`RepresentativeTransfer.clauseOne_representative_display` transports the
pointwise literal estimate of `ClauseOne` to the almost-sure,
`[0,infinity]`-valued display at the representative observables, and carries two
named slots:

* `hE2dom` — the real `(2,2)`-atom family is dominated by the display's
  `[0,infinity]`-valued supremum over the lattice annulus `3^n Z^d ∩ (□_j ∖
  □_{j−1})`;
* `hG1bdom` — the single shell sum `Σ_v 3^{−(s/2)v} A(m−v)^2` is dominated by
  the display's `n`-then-`k` double block sum.

Both are bookkeeping, not source gaps, and this module discharges them at the
*honest* lattice carriers.

## What is proved

* `ofReal_fmax_le_iSup` — the generic transfer: the `0`-floored finite maximum
  over a `Finset` of lattice indices, sent into `[0,infinity]`, is below the
  `[0,infinity]`-valued supremum over any set containing those indices.  No
  nonemptiness is needed (the empty maximum is `0`).
* `latticeAnnulusSet_nonempty` / `latticeAnnulusFinset_nonempty` — at spacing
  `3^n` with `n ≤ j − 1` the annulus `□_j ∖ □_{j−1}` does contain a lattice
  point, namely `3^{j−1} e_0`.
* `annularErrorLatticeMax`, `shellW2InfLatticeMax`, `shellBlockLatticeReal` —
  the real families the display's two slots are instantiated at, and their
  dominations `ofReal_annularErrorLatticeMax_le`,
  `ofReal_shellBlockLatticeReal_sq_le`.
* `ofReal_shellSingleSum_le_clauseOneTermFour` — the `hG1bdom` slot at
  **constant `1`**, by the distinct-slot injection `v ↦ n = m − v`: the shell
  `k = m − v` of the single sum is placed in the `n = m − v` slot of the double
  sum, where it is one summand of `Σ_{k ∈ [n−1, m]}` and carries *exactly* the
  single sum's own weight `3^{−(s/2)v}`.  The assignment is injective in `v`, so
  no slot is used twice.
* `clauseOne_representative_display_latticeMax` — the display with both slots
  discharged, i.e. depending only on the pointwise chain `hbound`.

## References

* ABK26, `p.mathcalE.annular.decomp` clause (i).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Homogenization Homogenization.Book Homogenization.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the generic maximum transfers -/

/-- **The `0`-floored finite maximum is attained**, above the floor, as soon as
the index set is nonempty and the entries are nonnegative. -/
theorem exists_mem_fmax_eq {iota : Type*} {S : Finset iota} (hS : S.Nonempty)
    {f : iota → ℝ} (hf : ∀ i ∈ S, 0 ≤ f i) :
    ∃ i ∈ S, Proportion.fmax S f = f i := by
  classical
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup S hS fun j => (f j).toNNReal
  refine ⟨i, hi, ?_⟩
  show ((S.sup fun j => (f j).toNNReal : ℝ≥0) : ℝ) = f i
  rw [hsup, Real.coe_toNNReal _ (hf i hi)]

/-- No nonemptiness enters — at the empty index set the left side is `0`. -/
theorem ofReal_fmax_le_iSup {iota : Type*} {S : Finset iota} {T : Set iota}
    (hST : ∀ i ∈ S, i ∈ T) (f : iota → ℝ) :
    ENNReal.ofReal (Proportion.fmax S f) ≤ ⨆ i : ↥T, ENNReal.ofReal (f i.1) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Proportion.fmax_empty, ENNReal.ofReal_zero]
    exact zero_le _
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup S hne fun j => (f j).toNNReal
    have hval : Proportion.fmax S f = max (f i) 0 := by
      show ((S.sup fun j => (f j).toNNReal : ℝ≥0) : ℝ) = max (f i) 0
      rw [hsup, Real.coe_toNNReal']
    rw [hval]
    rcases le_total 0 (f i) with h | h
    · rw [max_eq_left h]
      exact le_iSup (fun k : ↥T => ENNReal.ofReal (f k.1)) ⟨i, hST i hi⟩
    · rw [max_eq_right h, ENNReal.ofReal_zero]
      exact zero_le _

/-! ## Part B -- the lattice annulus is not empty -/

/-- **A triadic lattice point of spacing `3^n` inside `□_j ∖ □_{j−1}`.**  For
`n ≤ j − 1` the point `3^{j−1} e_0` is one: it lies strictly inside `□_j`
(whose half-width is `3^j/2 = (3/2) 3^{j−1}`) and strictly outside `□_{j−1}`
(whose half-width is `3^{j−1}/2`), and it is a lattice point because
`3^{j−1} = 3^n · 3^{j−1−n}`. -/
theorem latticeAnnulusSet_nonempty [NeZero d] {n j : ℤ} (hnj : n ≤ j - 1) :
    (Support.latticeAnnulusSet d n j (j - 1)).Nonempty := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = j - 1 - n :=
    ⟨(j - 1 - n).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
  have hsplit : (3 : ℝ) ^ j = (3 : ℝ) ^ (j - 1) * 3 := by
    rw [← zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hprod : (3 : ℝ) ^ n * (((3 : ℤ) ^ t : ℤ) : ℝ) = (3 : ℝ) ^ (j - 1) := by
    have hcast : (((3 : ℤ) ^ t : ℤ) : ℝ) = (3 : ℝ) ^ (t : ℤ) := by
      rw [zpow_natCast]
      norm_cast
    rw [hcast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), ht]
    congr 1
    ring
  have hval : ∀ i : Fin d,
      Support.triadicLatticePoint n (Pi.single (0 : Fin d) ((3 : ℤ) ^ t)) i
        = if i = (0 : Fin d) then (3 : ℝ) ^ (j - 1) else 0 := by
    intro i
    simp only [Support.triadicLatticePoint]
    by_cases hi : i = (0 : Fin d)
    · subst hi
      rw [Pi.single_eq_same, if_pos rfl, hprod]
    · rw [Pi.single_eq_of_ne hi, if_neg hi, Int.cast_zero, mul_zero]
  refine ⟨Pi.single (0 : Fin d) ((3 : ℤ) ^ t), ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    rw [hval i, hsplit]
    by_cases hi : i = (0 : Fin d)
    · rw [if_pos hi]
      exact ⟨by linarith only [h3], by linarith only [h3]⟩
    · rw [if_neg hi]
      exact ⟨by linarith only [h3], by linarith only [h3]⟩
  · intro hmem
    have hi0 := (mem_openCubeSet_originCube_iff.mp hmem) (0 : Fin d)
    rw [hval (0 : Fin d), if_pos rfl] at hi0
    linarith only [hi0.2, h3]

/-- The `Finset` reading of `latticeAnnulusSet_nonempty`. -/
theorem latticeAnnulusFinset_nonempty [NeZero d] {n j : ℤ} (hnj : n ≤ j - 1) :
    (Proportion.latticeAnnulusFinset d n j (j - 1)).Nonempty := by
  obtain ⟨v, hv⟩ := latticeAnnulusSet_nonempty (d := d) hnj
  exact ⟨v, (Proportion.mem_latticeAnnulusFinset_iff (by omega)).mpr hv⟩

/-! ## Part C -- the `hE2dom` slot -/

/-- **The `(2,2)` atom family of the display, as an honest finite maximum.**
The lattice maximum over `3^n Z^d ∩ (□_j ∖ □_{j−1})` of the squared annular
error observable, `0`-floored (which changes nothing: the entries are squares).
-/
def annularErrorLatticeMax (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) (j n : ℤ) : ℝ :=
  Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
    fun v => Support.annularErrorObservable M n s
      (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^ 2

theorem annularErrorLatticeMax_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    0 ≤ annularErrorLatticeMax M s omega j n :=
  Proportion.fmax_nonneg _ _

/-- Every lattice atom is below the maximum: the form a producer of the
`ClauseOne` chain consumes. -/
theorem le_annularErrorLatticeMax (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) {j n : ℤ} (hn : n ≤ j) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeAnnulusSet d n j (j - 1)) :
    Support.annularErrorObservable M n s
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^ 2
      ≤ annularErrorLatticeMax M s omega j n :=
  Proportion.le_fmax
    (f := fun v => Support.annularErrorObservable M n s
      (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^ 2)
    ((Proportion.mem_latticeAnnulusFinset_iff hn).mpr hv)

/-- **The maximum is attained** at a genuine lattice point of the annulus: with
`latticeAnnulusFinset_nonempty` this rules out the vacuous reading in which
`annularErrorLatticeMax` is the empty maximum `0`. -/
theorem exists_annularErrorLatticeMax_eq [NeZero d] (M : ABKModel d)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {j n : ℤ}
    (hnj : n ≤ j - 1) :
    ∃ v ∈ Proportion.latticeAnnulusFinset d n j (j - 1),
      annularErrorLatticeMax M s omega j n
        = Support.annularErrorObservable M n s
            (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) ^ 2 :=
  exists_mem_fmax_eq (latticeAnnulusFinset_nonempty hnj) fun _v _hv => sq_nonneg _

/-- **The `hE2dom` slot.**  The finite lattice maximum, sent into `[0,infinity]`, is
below the display's `[0,infinity]`-valued lattice supremum. -/
theorem ofReal_annularErrorLatticeMax_le (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) {j n : ℤ} (hn : n ≤ j) :
    ENNReal.ofReal (annularErrorLatticeMax M s omega j n)
      ≤ ⨆ v : ↥(Support.latticeAnnulusSet d n j (j - 1)),
          ENNReal.ofReal (Support.annularErrorObservable M n s
            (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v.1) omega) ^ 2) :=
  ofReal_fmax_le_iSup (fun _v hv => (Proportion.mem_latticeAnnulusFinset_iff hn).mp hv) _

/-! ## Part D -- the `hG1bdom` slot -/

/-- The `[0,infinity]`-valued shell block atom of the display's fourth term:
`3^{(2−γ)k} max_{z ∈ 3^k Z^d ∩ □_m} ‖j_k‖_{W^{2,∞}(z+□_k)}`. -/
def shellBlockLatticeAtom (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (k : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ ((2 - M.gamma) * (k : ℝ))) *
    ⨆ v : ↥(Support.latticeCubeSet d k m),
      ENNReal.ofReal (Support.shellW2InfNormAt
        (Support.triadicLatticePoint k v.1) k (omega.1 k))

/-- The `n`-slot of the display's fourth term. -/
def clauseOneTermFourSlot (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) (n : {n : ℤ // n ≤ m}) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ))) *
    ∑ k ∈ Finset.Icc (n.1 - 1) m, shellBlockLatticeAtom M m omega k ^ 2

theorem clauseOneTermFour_eq_tsum (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) :
    clauseOneTermFour M m s omega
      = ∑' n : {n : ℤ // n ≤ m}, clauseOneTermFourSlot M m s omega n :=
  rfl

/-- **The `hG1bdom` slot, at constant `1`.**

The single shell sum `Σ_{v ≥ 0} 3^{−(s/2)v} A(m−v)^2` is dominated by the
display's double block sum by the *distinct-slot injection* `v ↦ n = m − v`:

* the `n`-slot of the fourth term weighs `3^{−(s/2)(m−n)}`, which at `n = m − v`
  is exactly the single sum's own weight `3^{−(s/2)v}`;
* its inner sum runs over `k ∈ [n−1, m] = [m−v−1, m]`, which contains
  `k = m − v`, so the single sum's `v`-th atom is one of its summands;
* `v ↦ m − v` is injective, so no slot of the double sum is used twice.

No constant is lost.  The per-shell hypothesis `hA` is the atom-level
domination, discharged at the honest lattice carrier by
`ofReal_shellBlockLatticeReal_sq_le`. -/
theorem ofReal_shellSingleSum_le_clauseOneTermFour (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) {A : ℤ → ℝ}
    (hA : ∀ k : ℤ, k ≤ m →
      ENNReal.ofReal (A k ^ 2) ≤ shellBlockLatticeAtom M m omega k ^ 2) :
    ENNReal.ofReal
        (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2)
      ≤ clauseOneTermFour M m s omega := by
  classical
  have hinj : Function.Injective
      (fun v : ℕ => (⟨m - (v : ℤ), by omega⟩ : {n : ℤ // n ≤ m})) := by
    intro v w hvw
    have hval : m - (v : ℤ) = m - (w : ℤ) := congrArg Subtype.val hvw
    omega
  have hterm : ∀ v : ℕ,
      ENNReal.ofReal ((3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2)
        ≤ clauseOneTermFourSlot M m s omega ⟨m - (v : ℤ), by omega⟩ := by
    intro v
    have hexp : -(1 / 2 : ℝ) * (s : ℝ) * ((m - (m - (v : ℤ)) : ℤ) : ℝ)
        = -((s : ℝ) / 2) * (v : ℝ) := by
      push_cast
      ring
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    show ENNReal.ofReal ((3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)))
        * ENNReal.ofReal (A (m - (v : ℤ)) ^ 2)
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (s : ℝ) * ((m - (m - (v : ℤ)) : ℤ) : ℝ)))
        * ∑ k ∈ Finset.Icc (m - (v : ℤ) - 1) m, shellBlockLatticeAtom M m omega k ^ 2
    rw [hexp]
    refine mul_le_mul_right (le_trans (hA (m - (v : ℤ)) (by omega)) ?_) _
    exact Finset.single_le_sum
      (f := fun k => shellBlockLatticeAtom M m omega k ^ 2) (fun _i _hi => zero_le _)
      (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  calc ENNReal.ofReal
        (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2)
      ≤ ∑' v : ℕ,
          ENNReal.ofReal ((3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2) :=
        ofReal_tsum_le fun v =>
          mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
    _ ≤ ∑' v : ℕ, clauseOneTermFourSlot M m s omega ⟨m - (v : ℤ), by omega⟩ :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' n : {n : ℤ // n ≤ m}, clauseOneTermFourSlot M m s omega n :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj _
    _ = clauseOneTermFour M m s omega := (clauseOneTermFour_eq_tsum M m s omega).symm

/-! ## Part E -- the shell family at the honest lattice carrier -/

/-- The lattice maximum of the shell `W^{2,∞}` norms over `3^k Z^d ∩ □_m`. -/
def shellW2InfLatticeMax (m : ℤ) (omega : Cutoff.CutoffSample d) (k : ℤ) : ℝ :=
  Proportion.fmax (latticeCubeFinset d k m)
    fun v => Support.shellW2InfNormAt (Support.triadicLatticePoint k v) k (omega.1 k)

/-- The real shell block family `A(k) = 3^{(2−γ)k} max_z ‖j_k‖_{W^{2,∞}(z+□_k)}`
of the single shell sum. -/
def shellBlockLatticeReal (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (k : ℤ) : ℝ :=
  (3 : ℝ) ^ ((2 - M.gamma) * (k : ℝ)) * shellW2InfLatticeMax m omega k

theorem shellW2InfLatticeMax_nonneg (m : ℤ) (omega : Cutoff.CutoffSample d) (k : ℤ) :
    0 ≤ shellW2InfLatticeMax m omega k :=
  Proportion.fmax_nonneg _ _

theorem shellBlockLatticeReal_nonneg (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (k : ℤ) :
    0 ≤ shellBlockLatticeReal M m omega k :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (shellW2InfLatticeMax_nonneg m omega k)

/-- The real shell block family is dominated by the `[0,infinity]`-valued atom. -/
theorem ofReal_shellBlockLatticeReal_le (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) {k : ℤ} (hk : k ≤ m) :
    ENNReal.ofReal (shellBlockLatticeReal M m omega k)
      ≤ shellBlockLatticeAtom M m omega k := by
  simp only [shellBlockLatticeReal, shellBlockLatticeAtom, shellW2InfLatticeMax,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
  exact mul_le_mul_right
    (ofReal_fmax_le_iSup (fun _v hv => (mem_latticeCubeFinset_iff hk _).mp hv) _) _

/-- The squared form, i.e. the `hA` hypothesis of
`ofReal_shellSingleSum_le_clauseOneTermFour` at the honest lattice carrier. -/
theorem ofReal_shellBlockLatticeReal_sq_le (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) {k : ℤ} (hk : k ≤ m) :
    ENNReal.ofReal (shellBlockLatticeReal M m omega k ^ 2)
      ≤ shellBlockLatticeAtom M m omega k ^ 2 := by
  rw [ENNReal.ofReal_pow (shellBlockLatticeReal_nonneg M m omega k) 2]
  exact ENNReal.pow_le_pow_left (ofReal_shellBlockLatticeReal_le M m omega hk)

/-! ## Part F -- the display with both slots discharged -/

/-- **The clause-(i) representative display, at the lattice maxima.**

`clauseOne_representative_display` with its two slots discharged: the `(2,2)`
atom family is the finite lattice maximum `annularErrorLatticeMax` over `3^n
Z^d ∩ (□_j ∖ □_{j−1})`, and the single shell family is the finite lattice
maximum `shellBlockLatticeReal` over `3^k Z^d ∩ □_m`.  Only the pointwise chain
`hbound` — the output of `clauseOne_bound` at each `L` — remains.

The remaining hypothesis is a conditional A obligation, not a source premise;
no source node is claimed, realized or closed. -/
theorem clauseOne_representative_display_latticeMax [NeZero d] (M : ABKModel d)
    (m : ℤ) (s : {s : ℝ // 0 < s}) (Event : Set (Cutoff.CutoffSample d)) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hbound : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ Event → ∀ L : ℤ, m ≤ L →
        IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
          (annDouble m (fun j n =>
            (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
              * annularErrorLatticeMax M s omega j n))
          (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
          (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
            * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
          (s : ℝ) (Disorder.cstar M) M.gamma C) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Set.indicator Event (Support.fluxCorrectedErrorObservableSqSup M m s) omega
        ≤ ENNReal.ofReal (C * (s : ℝ)) * clauseOneTermOne M m s omega
          + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (3 : ℕ))
              * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)) * M.gamma ^ 2
              * |Real.log M.gamma| ^ 4)
          + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹
              * M.gamma) * clauseOneTermThree M m omega
          + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹
              * M.gamma) * clauseOneTermFour M m s omega :=
  clauseOne_representative_display (M := M) (m := m) (s := s) (Event := Event)
    (E2 := fun omega j n => annularErrorLatticeMax M s omega j n)
    (A := fun omega k => shellBlockLatticeReal M m omega k)
    hC0 (fun omega j n => annularErrorLatticeMax_nonneg M s omega j n) hbound
    (Filter.Eventually.of_forall fun omega j n _hj hn =>
      ofReal_annularErrorLatticeMax_le M s omega (by omega))
    (Filter.Eventually.of_forall fun omega =>
      ofReal_shellSingleSum_le_clauseOneTermFour M m s omega
        fun k hk => ofReal_shellBlockLatticeReal_sq_le M m omega hk)

end

end Algsuperdiff.Section4.Provider.Annular
