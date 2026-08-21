/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.Annular.Step3Arith
import Algsuperdiff.Section4.Support.Events

/-!
# Step 1 of the annular decomposition: the lattice cover and the centre term

ABK26, Section 4.1, `e.mathcalE.annular.decomp.pre`.  Step 1 turns a
full-grid weighted scale sum into an annular double sum.  Its two
ingredients are

2. the **centre-term resummation**: the centre `z = 0` contributes `J(□_n)`,
   which is pushed back into the annular shape by subadditivity plus the
   geometric factor `sum_{n=k+1}^{m} 3^(-2s(m-n) - d(n-1-k)) <=^(-2s(m-k))`.

This module proves both, plus the comparison of the diagonal slice of the
annular double sum with the double sum itself, and assembles them into
`Resum.IsAnnularDecompPre`.

## The honest range

The manuscript prints the claim for `s in (0, d/2]` and its proof writes `Since
s <= 1/2`.  Nothing is lost for the Section 4.1 caller, which uses `s <= 1/2`
and `d >= 2`.

## The two interchanges

The manuscript performs two order-of-summation interchanges.  The cover
interchange is carried here as the named slot `hcov` of `annularDecompPre_of`;
the centre interchange is what `centre_geom_factor` measures.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Homogenization
open Algsuperdiff.Section4.Support

noncomputable section

/-! ## Part A -- the lattice annular cover -/

section Geometry

variable {d : ℕ}

/-- The origin cubes are nested in the scale. -/
theorem openCubeSet_originCube_subset {k l : ℤ} (hkl : k ≤ l) :
    openCubeSet (originCube d k) ⊆ openCubeSet (originCube d l) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ l :=
    zpow_le_zpow_right₀ (by norm_num) hkl
  exact ⟨by linarith only [(hx i).1, h3], by linarith only [(hx i).2, h3]⟩

/-- **A nonzero scale-`n` lattice point is outside `□_n`.**  Its nonzero
coordinate has absolute value at least `3^n`, while `□_n` only reaches
`3^n / 2`. -/
theorem triadicLatticePoint_notMem_openCubeSet {n : ℤ} {v : Fin d → ℤ}
    (hv : v ≠ 0) :
    triadicLatticePoint n v ∉ openCubeSet (originCube d n) := by
  intro hmem
  rw [mem_openCubeSet_originCube_iff] at hmem
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (funext hc)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hval : triadicLatticePoint n v i = (3 : ℝ) ^ n * (v i : ℝ) := rfl
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hle : (v i : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    have := (hmem i).1
    rw [hval] at this
    have hmul : (3 : ℝ) ^ n * (v i : ℝ) ≤ (3 : ℝ) ^ n * (-1) :=
      mul_le_mul_of_nonneg_left hle h3.le
    linarith only [this, hmul, h3]
  · have hge : (1 : ℝ) ≤ (v i : ℝ) := by exact_mod_cast hpos
    have := (hmem i).2
    rw [hval] at this
    have hmul : (3 : ℝ) ^ n * 1 ≤ (3 : ℝ) ^ n * (v i : ℝ) :=
      mul_le_mul_of_nonneg_left hge h3.le
    linarith only [this, hmul, h3]

private theorem exists_annulus_aux {x : Vec d} :
    ∀ (t : ℕ) (k : ℤ), x ∈ openCubeSet (originCube d (k + (t : ℤ))) →
      x ∉ openCubeSet (originCube d k) →
      ∃ j : ℤ, k + 1 ≤ j ∧ j ≤ k + (t : ℤ) ∧
        x ∈ openCubeSet (originCube d j) ∧
        x ∉ openCubeSet (originCube d (j - 1)) := by
  intro t
  induction t with
  | zero =>
      intro k h1 h2
      rw [show k + ((0 : ℕ) : ℤ) = k by simp] at h1
      exact absurd h1 h2
  | succ t ih =>
      intro k h1 h2
      by_cases hb : x ∈ openCubeSet (originCube d (k + (t : ℤ)))
      · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih k hb h2
        exact ⟨j, hj1, by omega, hj3, hj4⟩
      · refine ⟨k + ((t + 1 : ℕ) : ℤ), by push_cast; omega, le_rfl, h1, ?_⟩
        have hrw : k + ((t + 1 : ℕ) : ℤ) - 1 = k + (t : ℤ) := by push_cast; ring
        rw [hrw]
        exact hb

/-- **The lattice annular cover**.

Every nonzero scale-`n` lattice point of `□_m` lies in exactly one triadic
annulus `□_j ∖ □_{j-1}` with `n + 1 <= j <= m`, namely the one indexed by the
least `j` with the point in `□_j`. -/
theorem exists_mem_latticeAnnulusSet {n m : ℤ} {v : Fin d → ℤ} (hv : v ≠ 0)
    (hmem : v ∈ latticeCubeSet d n m) :
    ∃ j : ℤ, n + 1 ≤ j ∧ j ≤ m ∧ v ∈ latticeAnnulusSet d n j (j - 1) := by
  have hin : triadicLatticePoint n v ∈ openCubeSet (originCube d m) := hmem
  have hout : triadicLatticePoint n v ∉ openCubeSet (originCube d n) :=
    triadicLatticePoint_notMem_openCubeSet hv
  have hnm : n ≤ m := by
    by_contra hc
    push_neg at hc
    exact hout (openCubeSet_originCube_subset (le_of_lt hc) hin)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m = n + (t : ℤ) := ⟨(m - n).toNat, by omega⟩
  subst ht
  obtain ⟨j, h1, h2, h3, h4⟩ := exists_annulus_aux t n hin hout
  exact ⟨j, h1, h2, ⟨h3, h4⟩⟩

/-- The centre `0` of the scale-`n` lattice is in `□_m` for every `n <= m`
(indeed for every `m`): the manuscript's `{0}` component of the cover. -/
theorem zero_mem_latticeCubeSet (n m : ℤ) : (0 : Fin d → ℤ) ∈ latticeCubeSet d n m := by
  show triadicLatticePoint n (0 : Fin d → ℤ) ∈ openCubeSet (originCube d m)
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hval : triadicLatticePoint n (0 : Fin d → ℤ) i = 0 := by
    simp only [triadicLatticePoint]
    norm_num
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  rw [hval]
  exact ⟨by linarith only [h3], by linarith only [h3]⟩

end Geometry

/-! ## Part B -- the centre-term geometric factor -/

/-- **The Step-1 geometric factor**, at the honest open range `2s < dd`.

Writing the centre resummation over the annulus index `i = n - k - 1`, the
weight sum is `sum_{i < N} 3^(-2s(N-1-i) - dd i)`, a geometric sum of ratio
`3^(2s - dd) < 1`; the bound is uniform in `N`. -/
theorem centre_geom_factor {s dd : ℝ} (hsd : 2 * s < dd) (N : ℕ) :
    ∑ i ∈ Finset.range N,
        (3 : ℝ) ^ (-(2 * s * (((N : ℤ) - 1 - (i : ℤ) : ℤ) : ℝ)) - dd * (i : ℝ))
      ≤ (3 : ℝ) ^ (2 * s) * (1 - (3 : ℝ) ^ (2 * s - dd))⁻¹
        * (3 : ℝ) ^ (-(2 * s * (N : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  set r : ℝ := (3 : ℝ) ^ (2 * s - dd) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hsd])
  have hterm : ∀ i ∈ Finset.range N,
      (3 : ℝ) ^ (-(2 * s * (((N : ℤ) - 1 - (i : ℤ) : ℤ) : ℝ)) - dd * (i : ℝ))
        = (3 : ℝ) ^ (2 * s) * (3 : ℝ) ^ (-(2 * s * (N : ℝ))) * r ^ i := by
    intro i _
    rw [hr, ← Real.rpow_natCast ((3 : ℝ) ^ (2 * s - dd)) i, ← Real.rpow_mul h3.le,
      ← Real.rpow_add h3, ← Real.rpow_add h3]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeo : ∑ i ∈ Finset.range N, r ^ i ≤ (1 - r)⁻¹ := by
    refine (Summable.sum_le_tsum (Finset.range N) (fun i _ => pow_nonneg hr0 _)
      (summable_geometric_of_lt_one hr0 hr1)).trans ?_
    exact (tsum_geometric_of_lt_one hr0 hr1).le
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * s) * (3 : ℝ) ^ (-(2 * s * (N : ℝ))) := by
    positivity
  calc (3 : ℝ) ^ (2 * s) * (3 : ℝ) ^ (-(2 * s * (N : ℝ))) * ∑ i ∈ Finset.range N, r ^ i
      ≤ (3 : ℝ) ^ (2 * s) * (3 : ℝ) ^ (-(2 * s * (N : ℝ))) * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo hpos
    _ = (3 : ℝ) ^ (2 * s) * (1 - r)⁻¹ * (3 : ℝ) ^ (-(2 * s * (N : ℝ))) := by ring

/-! ## Part C -- the diagonal slice of the annular double sum -/

private theorem diagIdx_injective (m : ℤ) :
    Function.Injective (fun p : ℕ × ℕ =>
      ((m - (p.1 : ℤ), m - (p.1 : ℤ) - 1 - (p.2 : ℤ)) : ℤ × ℤ)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨h1, h2⟩ := hab
  have ha : a = a' := by omega
  subst ha
  have hb : b = b' := by omega
  subst hb
  rfl

/-- **The diagonal slice of the annular double sum.**

The pairs `(j, j-1)` -- the innermost annulus at each scale -- form the `i = 0`
slice of the `N x N` parametrization, so their weighted sum is at most the
whole annular double sum.  This is what receives the resummed centre term (:
the relabelling `k -> n`, `k+1 -> j` proves at `n = j - 1`). -/
theorem tsum_diag_le_annDouble {m : ℤ} {h : ℤ → ℤ → ℝ}
    (hh0 : ∀ j n, 0 ≤ h j n) (hsum : Summable (annFam m h)) :
    ∑' u : ℕ, h (m - (u : ℤ)) (m - (u : ℤ) - 1) ≤ annDouble m h := by
  classical
  set H : ℕ × ℕ → ℝ :=
    fun p => h (m - (p.1 : ℤ)) (m - (p.1 : ℤ) - 1 - (p.2 : ℤ)) with hHdef
  have hHeq : ∀ p : ℕ × ℕ,
      annFam m h ((m - (p.1 : ℤ), m - (p.1 : ℤ) - 1 - (p.2 : ℤ)) : ℤ × ℤ) = H p := by
    rintro ⟨u, i⟩
    rw [annFam_apply, if_pos ⟨by omega, by omega⟩, hHdef]
  have hHsum : Summable H := by
    refine (hsum.comp_injective (diagIdx_injective m)).congr fun p => ?_
    exact hHeq p
  have hH0 : ∀ p : ℕ × ℕ, 0 ≤ H p := fun p => hh0 _ _
  have hinner : ∀ u : ℕ, h (m - (u : ℤ)) (m - (u : ℤ) - 1) ≤ ∑' i : ℕ, H (u, i) := by
    intro u
    have h0 : H (u, 0) = h (m - (u : ℤ)) (m - (u : ℤ) - 1) := by
      rw [hHdef]
      norm_num
    rw [← h0]
    have hsingle := Summable.sum_le_tsum (f := fun i : ℕ => H (u, i)) {0}
      (fun i _ => hH0 (u, i)) (hHsum.prod_factor u)
    rwa [Finset.sum_singleton] at hsingle
  have houter : Summable (fun u : ℕ => ∑' i : ℕ, H (u, i)) := hHsum.prod
  have hdiagSum : Summable (fun u : ℕ => h (m - (u : ℤ)) (m - (u : ℤ) - 1)) :=
    Summable.of_nonneg_of_le (fun u => hh0 _ _) hinner houter
  calc ∑' u : ℕ, h (m - (u : ℤ)) (m - (u : ℤ) - 1)
      ≤ ∑' u : ℕ, ∑' i : ℕ, H (u, i) :=
        Summable.tsum_le_tsum hinner hdiagSum houter
    _ = annDouble m h := (annDouble_eq_natIterated m h).symm

/-! ## Part D -- the Step-1 assembly -/

/-- **The Step-1 assembly**.

The manuscript's proof splits the full-grid weighted scale sum into the
annular-cover part and the centre part, bounds the first by the annular double
sum (the cover interchange, `hcov`) and pushes the second back into the
diagonal of the same double sum (the subadditivity iteration together with
`centre_geom_factor`, `hcen`).  The output is `Resum.IsAnnularDecompPre`, the
shape `Resum.preZero_of_pre_and_ugly` consumes.

Both slots are conditional A obligations on the caller: `hcov` is the cover
interchange and `hcen` the resummed centre term, whose constant is supplied by
`centre_geom_factor`. -/
theorem annularDecompPre_of {s Ccov Ccen C : ℝ} {m : ℤ} {Jgrid Jcen Jcov : ℤ → ℝ}
    {Jann : ℤ → ℤ → ℝ}
    (hJann0 : ∀ j n, 0 ≤ Jann j n) (hCcen : 0 ≤ Ccen)
    (hsum : Summable (annFam m
      (fun j n => (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jann j n)))
    (hgrid : ∀ n : ℤ, n ≤ m → Jgrid n ≤ Jcov n + Jcen n)
    (hcov : ∑' n : ℤ, (if n ≤ m then
        (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jcov n else 0)
      ≤ Ccov * annDouble m
          (fun j n => (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jann j n))
    (hcen : ∑' n : ℤ, (if n ≤ m then
        (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jcen n else 0)
      ≤ Ccen * ∑' u : ℕ,
          (3 : ℝ) ^ (-(2 * s * ((m - (m - (u : ℤ) - 1) : ℤ) : ℝ)))
            * Jann (m - (u : ℤ)) (m - (u : ℤ) - 1))
    (hsplit : Summable (fun n : ℤ =>
        (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jcov n else 0)))
    (hsplit2 : Summable (fun n : ℤ =>
        (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jcen n else 0)))
    (hJgrid0 : ∀ n, 0 ≤ Jgrid n)
    (hC : Ccov + Ccen ≤ C) :
    IsAnnularDecompPre s m Jgrid Jann C := by
  classical
  set w : ℤ → ℝ := fun n => (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) with hw
  set h : ℤ → ℤ → ℝ := fun j n => w n * Jann j n with hh
  have hh0 : ∀ j n, 0 ≤ h j n := fun j n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hJann0 j n)
  have hD0 : 0 ≤ annDouble m h := annDouble_nonneg hh0
  have hdiag := tsum_diag_le_annDouble (m := m) (h := h) hh0 hsum
  -- the split of the left-hand side
  have hleft : ∀ n : ℤ, (if n ≤ m then w n * Jgrid n else 0)
      ≤ (if n ≤ m then w n * Jcov n else 0) + (if n ≤ m then w n * Jcen n else 0) := by
    intro n
    by_cases hn : n ≤ m
    · rw [if_pos hn, if_pos hn, if_pos hn]
      have hwn : (0 : ℝ) ≤ w n := Real.rpow_nonneg (by norm_num) _
      have := mul_le_mul_of_nonneg_left (hgrid n hn) hwn
      linarith only [this]
    · rw [if_neg hn, if_neg hn, if_neg hn]
      norm_num
  have hgrid0 : ∀ n : ℤ, 0 ≤ (if n ≤ m then w n * Jgrid n else 0) := by
    intro n
    by_cases hn : n ≤ m
    · rw [if_pos hn]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hJgrid0 n)
    · rw [if_neg hn]
  have hsumTot : Summable (fun n : ℤ =>
      (if n ≤ m then w n * Jcov n else 0) + (if n ≤ m then w n * Jcen n else 0)) :=
    hsplit.add hsplit2
  have hgridSum : Summable (fun n : ℤ => (if n ≤ m then w n * Jgrid n else 0)) :=
    Summable.of_nonneg_of_le hgrid0 hleft hsumTot
  have hstep : ∑' n : ℤ, (if n ≤ m then w n * Jgrid n else 0)
      ≤ (∑' n : ℤ, (if n ≤ m then w n * Jcov n else 0))
        + ∑' n : ℤ, (if n ≤ m then w n * Jcen n else 0) := by
    calc ∑' n : ℤ, (if n ≤ m then w n * Jgrid n else 0)
        ≤ ∑' n : ℤ, ((if n ≤ m then w n * Jcov n else 0)
            + (if n ≤ m then w n * Jcen n else 0)) :=
          Summable.tsum_le_tsum hleft hgridSum hsumTot
      _ = (∑' n : ℤ, (if n ≤ m then w n * Jcov n else 0))
            + ∑' n : ℤ, (if n ≤ m then w n * Jcen n else 0) :=
          Summable.tsum_add hsplit hsplit2
  have hcen' : ∑' n : ℤ, (if n ≤ m then w n * Jcen n else 0)
      ≤ Ccen * annDouble m h :=
    hcen.trans (mul_le_mul_of_nonneg_left hdiag hCcen)
  unfold IsAnnularDecompPre
  have hfinal : (∑' n : ℤ, (if n ≤ m then w n * Jcov n else 0))
      + ∑' n : ℤ, (if n ≤ m then w n * Jcen n else 0)
      ≤ C * annDouble m h := by
    have h1 : (∑' n : ℤ, (if n ≤ m then w n * Jcov n else 0))
        + ∑' n : ℤ, (if n ≤ m then w n * Jcen n else 0)
        ≤ Ccov * annDouble m h + Ccen * annDouble m h := add_le_add hcov hcen'
    have h2 : Ccov * annDouble m h + Ccen * annDouble m h ≤ C * annDouble m h := by
      have := mul_le_mul_of_nonneg_right hC hD0
      linarith only [this]
    linarith only [h1, h2]
  have hgoal := hstep.trans hfinal
  rw [annDouble_def] at hgoal
  exact hgoal

end

end Algsuperdiff.Section4.Provider.Annular
