/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Regularity.RootAssemblyConditional
import Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow

namespace Algsuperdiff.Section4.Provider.Regularity

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The sharp criterion for the cube gate -/

/-- **The cube gate from the coordinate gaps.**  If every coordinate of `z` clears
`½·3^m − ½·3^q`, the translated cube `z + □_q` sits inside `□_m`. -/
theorem image_add_subset_openCubeSet_of_forall_abs_le {m q : ℤ} {z : Vec d}
    (h : ∀ i : Fin d,
      |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    (fun y => z + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m) := by
  rintro p ⟨w, hw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hw
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hwi := hw i
  have hi := h i
  have hz1 : z i ≤ |z i| := le_abs_self _
  have hz2 : -(z i) ≤ |z i| := neg_le_abs _
  simp only [Pi.add_apply]
  exact ⟨by linarith only [hwi.1, hi, hz2], by linarith only [hwi.2, hi, hz1]⟩

/-- The upper half of the converse: the gate forces every coordinate to clear the
gap on the right.  The escaping point is exhibited explicitly. -/
private theorem coord_le_of_image_add_subset {m q : ℤ} {z : Vec d}
    (h : (fun y => z + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m)) (i : Fin d) :
    z i + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  classical
  by_contra hcon
  push_neg at hcon
  have hQ : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ q := by
    have := zpow_pos (by norm_num : (0 : ℝ) < 3) q
    linarith only [this]
  set a : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - z i with hadef
  have ha : a < (1 / 2 : ℝ) * (3 : ℝ) ^ q := by rw [hadef]; linarith only [hcon]
  set t : ℝ := (max a 0 + (1 / 2 : ℝ) * (3 : ℝ) ^ q) / 2 with htdef
  have hmax1 : a ≤ max a 0 := le_max_left _ _
  have hmax2 : (0 : ℝ) ≤ max a 0 := le_max_right _ _
  have hmax3 : max a 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ q := max_lt ha hQ
  have ht1 : t < (1 / 2 : ℝ) * (3 : ℝ) ^ q := by rw [htdef]; linarith only [hmax3]
  have ht0 : (0 : ℝ) < t := by rw [htdef]; linarith only [hmax2, hQ]
  have hta : a ≤ t := by rw [htdef]; linarith only [hmax1, ha]
  have hw : (fun _ => t : Vec d) ∈ openCubeSet (originCube d q) := by
    rw [mem_openCubeSet_originCube_iff]
    exact fun _ => ⟨by linarith only [ht0, hQ], ht1⟩
  have hmem := h ⟨_, hw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hmem
  have hi : z i + t < (1 / 2 : ℝ) * (3 : ℝ) ^ m := (hmem i).2
  rw [hadef] at hta
  linarith only [hi, hta]

/-- The `z ↦ -z` symmetry of the gate: the origin cubes are symmetric, so a
translate fits on one side exactly when its reflection fits on the other. -/
private theorem image_add_subset_openCubeSet_neg {m q : ℤ} {z : Vec d}
    (h : (fun y => z + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m)) :
    (fun y => (-z) + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m) := by
  rintro p ⟨w, hw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hw
  have hnw : (-w : Vec d) ∈ openCubeSet (originCube d q) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi := hw i
    simp only [Pi.neg_apply]
    exact ⟨by linarith only [hi.2], by linarith only [hi.1]⟩
  have hmem := h ⟨-w, hnw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hmem ⊢
  intro i
  have hi := hmem i
  simp only [Pi.add_apply, Pi.neg_apply] at hi ⊢
  exact ⟨by linarith only [hi.2], by linarith only [hi.1]⟩

/-- **The gate criterion, both directions.**  `z + □_q ⊆ □_m` holds exactly when
every coordinate of `z` clears the gap `½·3^m − ½·3^q`. -/
theorem image_add_subset_openCubeSet_iff {m q : ℤ} {z : Vec d} :
    ((fun y => z + y) '' openCubeSet (originCube d q) ⊆
        openCubeSet (originCube d m)) ↔
      ∀ i : Fin d, |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  refine ⟨fun h i => ?_, image_add_subset_openCubeSet_of_forall_abs_le⟩
  have hup := coord_le_of_image_add_subset h i
  have hlo := coord_le_of_image_add_subset (image_add_subset_openCubeSet_neg h) i
  simp only [Pi.neg_apply] at hlo
  rcases le_or_gt 0 (z i) with hz | hz
  · rw [abs_of_nonneg hz]; exact hup
  · rw [abs_of_neg hz]; exact hlo

/-- **The gate whenever one coordinate does not clear the gap.**  This is the
contrapositive of the criterion, isolated because it is the statement that
closes the boundary branch off: at a centre with `|z_i| + ½·3^q > ½·3^m` no
argument can produce the untruncated gate. -/
theorem not_image_add_subset_openCubeSet_of_lt {m q : ℤ} {z : Vec d} {i : Fin d}
    (hi : (1 / 2 : ℝ) * (3 : ℝ) ^ m < |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ q) :
    ¬ ((fun y => z + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m)) := by
  intro h
  have := (image_add_subset_openCubeSet_iff.mp h) i
  linarith only [this, hi]

/-! ## 2. The producer at a general printed lattice centre -/

/-- **The integrality gap of a printed lattice centre.**  A point of `3^n ℤ^d` that
lies in `□_m` (with `n ≤ m`) clears the gap at scale `n`: `|z_i| ≤ ½(3^m −
3^n)`.  The proof is the integer step `2|v_i| < 3^{m-n} ⟹ 2|v_i| ≤ 3^{m-n} −
1`, so this is an arithmetic fact about the lattice and not an interiority
assumption. -/
theorem abs_triadicLatticePoint_add_le {n m : ℤ} (hnm : n ≤ m) {v : Fin d → ℤ}
    (hv : Support.triadicLatticePoint n v ∈ openCubeSet (originCube d m))
    (i : Fin d) :
    |Support.triadicLatticePoint n v i| + (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  have hNdef : m = n + ((m - n).toNat : ℤ) := by omega
  set N : ℕ := (m - n).toNat with hN
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hsplit : (3 : ℝ) ^ m = (3 : ℝ) ^ n * (3 : ℝ) ^ N := by
    rw [show (m : ℤ) = n + (N : ℤ) from hNdef, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      zpow_natCast]
  have hvi := (mem_openCubeSet_originCube_iff.mp hv) i
  have hpt : Support.triadicLatticePoint n v i = (3 : ℝ) ^ n * ((v i : ℤ) : ℝ) := rfl
  rw [hpt] at hvi ⊢
  have habs : |(3 : ℝ) ^ n * ((v i : ℤ) : ℝ)| = (3 : ℝ) ^ n * |((v i : ℤ) : ℝ)| := by
    rw [abs_mul, abs_of_pos h3n]
  -- the real bound `2|v_i| < 3^N`
  have hreal : 2 * |((v i : ℤ) : ℝ)| < (3 : ℝ) ^ N := by
    have hab : |(3 : ℝ) ^ n * ((v i : ℤ) : ℝ)| < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
      abs_lt.mpr ⟨by linarith only [hvi.1], hvi.2⟩
    rw [habs, hsplit] at hab
    have := (mul_lt_mul_iff_of_pos_left h3n).mp
      (by linarith only [hab] :
        (3 : ℝ) ^ n * (2 * |((v i : ℤ) : ℝ)|) < (3 : ℝ) ^ n * (3 : ℝ) ^ N)
    exact this
  -- the integer step
  have hint : (2 * |v i| : ℤ) < (3 : ℤ) ^ N := by
    have hcast : ((2 * |v i| : ℤ) : ℝ) < (((3 : ℤ) ^ N : ℤ) : ℝ) := by
      push_cast
      push_cast at hreal
      linarith only [hreal]
    exact_mod_cast hcast
  have hint' : (2 * |v i| : ℤ) ≤ (3 : ℤ) ^ N - 1 := by omega
  have hback : 2 * |((v i : ℤ) : ℝ)| ≤ (3 : ℝ) ^ N - 1 := by
    have : ((2 * |v i| : ℤ) : ℝ) ≤ (((3 : ℤ) ^ N - 1 : ℤ) : ℝ) := by exact_mod_cast hint'
    push_cast at this
    linarith only [this]
  rw [habs]
  have hmul : (3 : ℝ) ^ n * (2 * |((v i : ℤ) : ℝ)|) ≤ (3 : ℝ) ^ n * ((3 : ℝ) ^ N - 1) :=
    mul_le_mul_of_nonneg_left hback h3n.le
  have hexp : (3 : ℝ) ^ n * ((3 : ℝ) ^ N - 1) = (3 : ℝ) ^ m - (3 : ℝ) ^ n := by
    rw [hsplit]; ring
  linarith only [hmul, hexp]

/-- **The cube gate at a general printed lattice centre.**

For `z = 3^n v ∈ □_m` — with NO interiority hypothesis, so `z ∉ □_{m-1}` is
allowed — every scale `q ≤ n` is gated:

```text
   z + □_q ⊆ □_m .
```

`§1`'s criterion shows the bound `q ≤ n` is the whole of what the lattice alone
buys: a centre with `|z_i| = ½(3^m − 3^n)` fails the gate at every `q > n`. -/
theorem image_add_subset_openCubeSet_of_latticeCentre {n m q : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ}
    (hv : Support.triadicLatticePoint n v ∈ openCubeSet (originCube d m))
    (hq : q ≤ n) :
    (fun y => Support.triadicLatticePoint n v + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m) := by
  refine image_add_subset_openCubeSet_of_forall_abs_le fun i => ?_
  have hmono : (3 : ℝ) ^ q ≤ (3 : ℝ) ^ n := zpow_le_zpow_right₀ (by norm_num) hq
  have := abs_triadicLatticePoint_add_le hnm hv i
  linarith only [this, hmono]

/-- **The same producer at the root's own off-grid centre.**  `offGridCentre n x`
is a printed lattice centre of spacing `3^n`, and it inherits `x`'s membership
in `□_m`, so no interiority hypothesis on `x` is needed either. -/
theorem image_add_subset_openCubeSet_of_offGridCentre {n m q : ℤ} (hnm : n ≤ m)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hq : q ≤ n) :
    (fun y => offGridCentre n x + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m) :=
  image_add_subset_openCubeSet_of_latticeCentre hnm
    (v := offGridLatticeIndex n x) (offGridCentre_mem_openCubeSet n hx) hq

/-- **The Step-4 slot's own gate index.**'s slot at scale `j` asks for `z + □_{j-2}
⊆ □_m`; at a printed lattice centre of spacing `3^n` that is available exactly
on the scales `j ≤ n + 2`. -/
theorem stepFourCubeGate_of_latticeCentre {n m j : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ}
    (hv : Support.triadicLatticePoint n v ∈ openCubeSet (originCube d m))
    (hj : j ≤ n + 2) :
    (fun y => Support.triadicLatticePoint n v + y) ''
        openCubeSet (originCube d (j - 2)) ⊆
      openCubeSet (originCube d m) :=
  image_add_subset_openCubeSet_of_latticeCentre hnm hv (by omega)

/-- **The bound `q ≤ n` of `image_add_subset_openCubeSet_of_latticeCentre` is
sharp**, and sharp by an explicit witness rather than by an abstract argument.

The extreme printed lattice centre `z = 3^n·((3^{m-n}-1)/2)·(1,…,1)` lies in
`□_m` and its coordinates sit at exactly `½(3^m − 3^n)`, so `z + □_q ⊆ □_m` at
every `q > n`.  Consequently the untruncated gate is genuinely unavailable on
the deep scales at boundary centres: no strengthening of the producer can reach
them. -/
theorem exists_latticeCentre_gate_fails (d : ℕ) [NeZero d] {n m : ℤ} (hnm : n ≤ m) :
    ∃ v : Fin d → ℤ,
      Support.triadicLatticePoint n v ∈ openCubeSet (originCube d m) ∧
        ∀ q : ℤ, n < q →
          ¬ ((fun y => Support.triadicLatticePoint n v + y) ''
              openCubeSet (originCube d q) ⊆ openCubeSet (originCube d m)) := by
  have hNdef : m = n + (((m - n).toNat : ℕ) : ℤ) := by omega
  set N : ℕ := (m - n).toNat with hN
  obtain ⟨a, ha⟩ : Odd ((3 : ℤ) ^ N) := Odd.pow ⟨1, by norm_num⟩
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hsplit : (3 : ℝ) ^ m = (3 : ℝ) ^ n * (3 : ℝ) ^ N := by
    rw [show (m : ℤ) = n + (N : ℤ) from hNdef, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      zpow_natCast]
  have hacast : 2 * ((a : ℤ) : ℝ) = (3 : ℝ) ^ N - 1 := by
    have hR : (((3 : ℤ) ^ N : ℤ) : ℝ) = ((2 * a + 1 : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ha
    push_cast at hR
    linarith only [hR]
  have hval : Support.triadicLatticePoint n (fun _ => a) =
      (fun _ => (3 : ℝ) ^ n * ((a : ℤ) : ℝ) : Vec d) := rfl
  have hcoord : (3 : ℝ) ^ n * ((a : ℤ) : ℝ) =
      ((3 : ℝ) ^ m - (3 : ℝ) ^ n) / 2 := by
    have hmul : (3 : ℝ) ^ n * (2 * ((a : ℤ) : ℝ)) =
        (3 : ℝ) ^ n * ((3 : ℝ) ^ N - 1) := by rw [hacast]
    rw [hsplit]
    linarith only [hmul]
  have hnm3 : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hnm
  refine ⟨fun _ => a, ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    rw [hval]
    exact ⟨by rw [hcoord]; linarith only [h3n, hnm3],
      by rw [hcoord]; linarith only [h3n]⟩
  · intro q hq
    refine not_image_add_subset_openCubeSet_of_lt
      (i := (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)) ?_
    have hqmono : (3 : ℝ) ^ n < (3 : ℝ) ^ q :=
      zpow_lt_zpow_right₀ (by norm_num) hq
    have habs : |Support.triadicLatticePoint n (fun _ => a)
        (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)| =
        ((3 : ℝ) ^ m - (3 : ℝ) ^ n) / 2 := by
      rw [hval]
      simp only []
      rw [hcoord, abs_of_nonneg (by linarith only [hnm3] :
        (0 : ℝ) ≤ ((3 : ℝ) ^ m - (3 : ℝ) ^ n) / 2)]
    rw [habs]
    linarith only [hqmono]

/-! ## 3. The truncated form, and the join's geometric half -/

/-- **The truncated window is untruncated exactly on the gated scales.**  This is
the dichotomy in the carrier the chain uses: `(z + □_q) ∩ □_m = z + □_q` iff
the gate holds, and otherwise the intersection is a subset. -/
theorem truncatedWindow_eq_image_add_iff {m q : ℤ} {z : Vec d} :
    truncatedWindow z m q = (fun y => z + y) '' openCubeSet (originCube d q) ↔
      (fun y => z + y) '' openCubeSet (originCube d q) ⊆
        openCubeSet (originCube d m) :=
  Set.inter_eq_left

theorem truncatedWindow_eq_image_add_of_latticeCentre {n m q : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ}
    (hv : Support.triadicLatticePoint n v ∈ openCubeSet (originCube d m))
    (hq : q ≤ n) :
    truncatedWindow (Support.triadicLatticePoint n v) m q =
      (fun y => Support.triadicLatticePoint n v + y) ''
        openCubeSet (originCube d q) :=
  truncatedWindow_eq_image_add_iff.mpr
    (image_add_subset_openCubeSet_of_latticeCentre hnm hv hq)

/-- **The join's window hypothesis holds centre scale.**

`ExcessDecay.excessDecay_oneStep_anchored` replaces the interior gate by the
disjunction "gate OR a met face of `∂□_m`"; its geometric half is a tautology,
because a window that meets no face of `∂□_m` in any coordinate clears the gap
in every coordinate.  So the boundary `hstep4` run owes the geometry nothing:
what it still needs from the join's second disjunct is the competitor data (the
`MemLp` clauses, met-face oddness and classical harmonicity on the doubled
window), which is analytic. -/
theorem gate_or_exists_meetsFace (z : Vec d) (m q : ℤ) :
    ((fun y => z + y) '' openCubeSet (originCube d q) ⊆
        openCubeSet (originCube d m)) ∨
      ∃ i : Fin d, MeetsUpperFace z m q i ∨ MeetsLowerFace z m q i := by
  classical
  by_cases h : ∀ i : Fin d,
      |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m
  · exact Or.inl (image_add_subset_openCubeSet_of_forall_abs_le h)
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    refine Or.inr ⟨i, ?_⟩
    rcases le_or_gt 0 (z i) with hz | hz
    · left
      show (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ z i + (1 / 2 : ℝ) * (3 : ℝ) ^ q
      rw [abs_of_nonneg hz] at hi
      linarith only [hi]
    · right
      show z i - (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m
      rw [abs_of_neg hz] at hi
      linarith only [hi]

end

end Algsuperdiff.Section4.Provider.Regularity
