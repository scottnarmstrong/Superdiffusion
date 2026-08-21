/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryPoincareCore
import Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryTraceMeasure

/-!
# The boundary Poincaré inequality on the anchor window

On the boundary branch of the general clause, where

```text
  (z + □_{n+2}) ∩ ∂□_m ≠ ∅ ,
```

an `H¹₀(□_m)` datum obeys the `L²` Poincaré inequality **at the window scale**
on the anchor's own window `W' = (z + □_{n+3}) ∩ □_m`:

```text
  ‖u‖_{L²(W')} ≤ C(d) · 3ⁿ · Σᵢ ‖∂ᵢu‖_{L²(W')} ,
      C(d) = 27 (1 + √3) · unitMeanZeroPoincareConst d .
```

The three ingredients:

* `overhang_of_frontier_ne_empty` — the negated gate is *quantitative*: the
  parent cube `z + □_{n+2}` pokes strictly out of `□_m` in some coordinate `i`
  and some direction `σ = ±1`, i.e. `½·3^m < σ zᵢ + ½·3^{n+2}`.  (The frontier
  of an open set is disjoint from it, so a point of the intersection is a point
  of the parent cube outside `□_m`.)
* `volume_le_three_mul_boundarySlab` — the zero extension of the datum vanishes
  on the slab `E = (z + □_{n+3}) ∩ {½·3^m ≤ σ yᵢ}`, and the overhang bound makes
  that slab at least a **third** of the cube.  This is where the window
  enlargement pays: at `n+2` the overhang can be arbitrarily thin, at `n+3` it
  is at least `3^{n+2}` deep against a side of `3^{n+3}`.
* `BoundaryPoincareCore` — the zero-set Poincaré on the enclosing cube.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem volumeMeasureOn_eq_restrict_window (U : Set (Vec d)) :
    volumeMeasureOn U = volume.restrict U := rfl

/-! ## 1. The translated open cube as an axis cube -/

/-- Membership in a translated open triadic cube, coordinatewise. -/
theorem mem_image_add_openCubeSet_iff {j : ℤ} {z y : Vec d} :
    y ∈ (fun y' => z + y') '' openCubeSet (originCube d j) ↔
      ∀ i, (-(1 / 2 : ℝ)) * (3 : ℝ) ^ j < y i - z i ∧
        y i - z i < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro i
    simpa using mem_openCubeSet_originCube_iff.mp hw i
  · intro h
    refine ⟨y - z, mem_openCubeSet_originCube_iff.mpr ?_, ?_⟩
    · intro i
      simpa using h i
    · funext i
      simp

/-- Membership in an axis cube, coordinatewise. -/
theorem mem_axisCube_iff {c : Vec d} {L : ℝ} {y : Vec d} :
    y ∈ axisCube c L ↔ ∀ j, c j < y j ∧ y j < c j + L := by
  simp [axisCube, Set.mem_pi, Set.mem_Ioo]

theorem image_add_openCubeSet_eq_axisCube (z : Vec d) (j : ℤ) :
    (fun y' => z + y') '' openCubeSet (originCube d j) =
      axisCube (fun i => z i - (1 / 2 : ℝ) * (3 : ℝ) ^ j) ((3 : ℝ) ^ j) := by
  ext y
  rw [mem_image_add_openCubeSet_iff, mem_axisCube_iff]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩

/-! ## 2. The negated gate, quantitatively -/

/-- **The boundary branch pokes out.**

If the parent cube `z + □_j` meets the frontier of `□_m`, then in some
coordinate `i` and some direction `σ = ±1` it strictly exceeds the half-width of
`□_m`.  This is the quantitative form of the anchor's *negated* interior gate. -/
theorem overhang_of_frontier_ne_empty {j m : ℤ} {z : Vec d}
    (hfr : (((fun y' => z + y') '' openCubeSet (originCube d j)) ∩
      frontier (openCubeSet (originCube d m))) ≠ ∅) :
    ∃ (i : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧
      (1 / 2 : ℝ) * (3 : ℝ) ^ m < σ * z i + (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  classical
  obtain ⟨p, hpcube, hpfr⟩ := Set.nonempty_iff_ne_empty.mpr hfr
  have hpout : p ∉ openCubeSet (originCube d m) := by
    rw [(isOpen_openCubeSet (originCube d m)).frontier_eq] at hpfr
    exact hpfr.2
  have hp : ∃ i, ¬((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < p i ∧
      p i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
    by_contra hcon
    push_neg at hcon
    exact hpout (mem_openCubeSet_originCube_iff.mpr fun i => hcon i)
  obtain ⟨i, hi⟩ := hp
  obtain ⟨hlo, hhi⟩ := mem_image_add_openCubeSet_iff.mp hpcube i
  rcases not_and_or.mp hi with hcase | hcase
  · push_neg at hcase
    exact ⟨i, -1, Or.inr rfl, by linarith only [hcase, hlo]⟩
  · push_neg at hcase
    exact ⟨i, 1, Or.inl rfl, by linarith only [hcase, hhi]⟩

/-! ## 3. The slab is a third of the enclosing cube -/

/-- **The overhang slab carries a third of the `n+3` cube.**

The heart of the window enlargement: whatever the configuration, the part
of `z + □_{n+3}` lying beyond the frontier level `½·3^m` of `□_m` in the
direction `σ eᵢ` is at least a third of the cube.  Proof: three translates of
the slab cover the cube. -/
theorem volume_le_three_mul_boundarySlab {n m : ℤ} {z : Vec d} {σ : ℝ}
    {i : Fin d} (hσ : σ = 1 ∨ σ = -1)
    (hover : (1 / 2 : ℝ) * (3 : ℝ) ^ m <
      σ * z i + (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 2)) :
    volume (axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
        ((3 : ℝ) ^ (n + 3))) ≤
      3 * volume ((axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
          ((3 : ℝ) ^ (n + 3))) ∩
        {y | (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ σ * y i}) := by
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ (n + 3) := zpow_pos (by norm_num) _
  have h32 : (3 : ℝ) ^ (n + 3) = 3 * (3 : ℝ) ^ (n + 2) := by
    rw [show n + 3 = (n + 2) + 1 by ring,
      zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hsq : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  refine volume_le_three_mul_slab (g := fun y => σ * y i) (e := σ • basisVec i)
    (lo := σ * z i - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
    (hi := σ * z i + (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3)) ?_ ?_ ?_ ?_ ?_
  · intro y s
    have hcoord : (y + s • (σ • basisVec i)) i = y i + s * σ := by
      simp [basisVec_apply]
    simp only [hcoord]
    rw [show σ * (y i + s * σ) = σ * y i + s * (σ * σ) by ring, hsq, mul_one]
  · intro y hy
    rw [mem_axisCube_iff] at hy
    obtain ⟨h1, h2⟩ := hy i
    rcases hσ with h | h <;> subst h <;>
      exact ⟨by simp only [one_mul, neg_mul]; linarith only [h1, h2],
        by simp only [one_mul, neg_mul]; linarith only [h1, h2]⟩
  · intro y hy s hs1 hs2
    rw [mem_axisCube_iff] at hy ⊢
    intro j
    by_cases hj : j = i
    · subst hj
      obtain ⟨h1, h2⟩ := hy j
      have hcoord : (y + s • (σ • basisVec j)) j = y j + s * σ := by
        simp [basisVec_apply]
      simp only [hcoord]
      simp only at h1 h2 hs1 hs2 ⊢
      rcases hσ with h | h <;> subst h <;> simp only [one_mul, neg_mul] at hs1 hs2 ⊢ <;>
        exact ⟨by linarith only [hs1, hs2], by linarith only [hs1, hs2]⟩
    · obtain ⟨h1, h2⟩ := hy j
      have hcoord : (y + s • (σ • basisVec i)) j = y j := by
        simp [basisVec_apply, hj]
      simp only [hcoord]
      exact ⟨h1, h2⟩
  · linarith only [hover, h32, hLpos]
  · linarith only [hover, h32]

/-! ## 4. The boundary Poincaré constant and the estimate -/

/-- The coefficient-free constant of the boundary window Poincaré inequality:
`27 (1 + √3)` times the `d`-only mean-zero constant of the unit corner cube. -/
def boundaryWindowPoincareConst (d : ℕ) : ℝ :=
  (1 + Real.sqrt 3) * (unitMeanZeroPoincareConst d * 27)

theorem boundaryWindowPoincareConst_nonneg (d : ℕ) :
    0 ≤ boundaryWindowPoincareConst d := by
  have h1 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h2 : 0 ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  have h3 : 0 ≤ unitMeanZeroPoincareConst d * 27 := by linarith only [h2]
  exact mul_nonneg (by linarith only [h1]) h3

/-- **The boundary Poincaré inequality on the anchor window.**

On the boundary branch of the general clause, an `H¹₀(□_m)` datum obeys the
un-subtracted `L²` Poincaré inequality at the window scale on the anchor's own
window `W' = (z + □_{n+3}) ∩ □_m`, with a constant depending on `d` alone. -/
theorem eLpNorm_le_boundaryWindowPoincare {n m : ℤ} {z : Vec d}
    (hfr : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      frontier (openCubeSet (originCube d m))) ≠ ∅)
    (u : H10Function (openCubeSet (originCube d m))) :
    (eLpNorm u.toFun 2 (volume.restrict
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal ≤
      boundaryWindowPoincareConst d * (3 : ℝ) ^ n *
        ∑ i : Fin d,
          (eLpNorm (fun x => u.grad x i) 2 (volume.restrict
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  classical
  obtain ⟨i, σ, hσ, hover⟩ := overhang_of_frontier_ne_empty hfr
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ (n + 3) := zpow_pos (by norm_num) _
  have h3n : (3 : ℝ) ^ (n + 3) = 27 * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    (isOpen_openCubeSet (originCube d m)).measurableSet
  rw [image_add_openCubeSet_eq_axisCube z (n + 3)]
  have hEmeas : MeasurableSet
      ((axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
          ((3 : ℝ) ^ (n + 3))) ∩ {y | (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ σ * y i}) :=
    (isOpen_axisCube _ _).measurableSet.inter
      (measurableSet_le measurable_const
        (measurable_const.mul (measurable_pi_apply i)))
  have hzeroE : ∀ y ∈ (axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
        ((3 : ℝ) ^ (n + 3))) ∩ {y | (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ σ * y i},
      (zeroExtendH1 hmeas u
        (axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
          ((3 : ℝ) ^ (n + 3)))).toFun y = 0 := by
    intro y hy
    refine zeroExtendH1_eq_zero_of_notMem hmeas u _ ?_
    intro hmem
    obtain ⟨h1, h2⟩ := mem_openCubeSet_originCube_iff.mp hmem i
    have hy2 : (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ σ * y i := hy.2
    rcases hσ with h | h <;> subst h <;> simp only [one_mul, neg_mul] at hy2 <;>
      linarith only [h1, h2, hy2]
  have hvolE : volume (axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
        ((3 : ℝ) ^ (n + 3))) ≤
      ENNReal.ofReal 3 *
        volume ((axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
            ((3 : ℝ) ^ (n + 3))) ∩
          {y | (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ σ * y i}) := by
    have h3 : ENNReal.ofReal (3 : ℝ) = 3 := by
      simp
    rw [h3]
    exact volume_le_three_mul_boundarySlab hσ hover
  have hcore := eLpNorm_le_of_zeroSet_of_volume_le
    (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3)) hLpos
    (by norm_num : (0 : ℝ) ≤ 3)
    (zeroExtendH1 hmeas u
      (axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
        ((3 : ℝ) ^ (n + 3))))
    Set.inter_subset_left hEmeas hzeroE hvolE
  rw [volumeMeasureOn_eq_restrict_window, zeroExtendH1_toFun,
    eLpNorm_zeroExtend_eq hmeas] at hcore
  have hgrads : ∀ k : Fin d,
      eLpNorm (fun x => (zeroExtendH1 hmeas u
          (axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
            ((3 : ℝ) ^ (n + 3)))).grad x k) 2
        (volumeMeasureOn (axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
          ((3 : ℝ) ^ (n + 3)))) =
      eLpNorm (fun x => u.grad x k) 2
        (volume.restrict
          ((axisCube (fun j => z j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3))
            ((3 : ℝ) ^ (n + 3))) ∩ openCubeSet (originCube d m))) := by
    intro k
    rw [volumeMeasureOn_eq_restrict_window, zeroExtendH1_grad,
      eLpNorm_zeroExtendGrad_eq hmeas]
  simp only [hgrads] at hcore
  have hconst : (1 + Real.sqrt 3) *
      (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 3)) =
      boundaryWindowPoincareConst d * (3 : ℝ) ^ n := by
    rw [boundaryWindowPoincareConst, h3n]
    ring
  rw [← hconst]
  exact hcore

end

end Algsuperdiff.Section4.Provider.ExcessDecay
